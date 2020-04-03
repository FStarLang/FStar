open Prims
let cases :
  'Auu____10 'Auu____11 .
    ('Auu____10 -> 'Auu____11) ->
      'Auu____11 -> 'Auu____10 FStar_Pervasives_Native.option -> 'Auu____11
  =
  fun f  ->
    fun d  ->
      fun uu___0_31  ->
        match uu___0_31 with
        | FStar_Pervasives_Native.Some x -> f x
        | FStar_Pervasives_Native.None  -> d
  
type closure =
  | Clos of ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option *
  closure) Prims.list * FStar_Syntax_Syntax.term *
  ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
  Prims.list * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo *
  Prims.bool) 
  | Univ of FStar_Syntax_Syntax.universe 
  | Dummy 
let (uu___is_Clos : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Clos _0 -> true | uu____155 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____267 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____285 -> false
  
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
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____493 -> false
  
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____536 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____579 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____624 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____679 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____742 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_CBVApp : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | CBVApp _0 -> true | uu____793 -> false
  
let (__proj__CBVApp__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee  -> match projectee with | CBVApp _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____842 -> false
  
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____887 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____930 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____953 -> false
  
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____982 = FStar_Syntax_Util.head_and_args' t  in
    match uu____982 with | (hd1,uu____998) -> hd1
  
let mk :
  'Auu____1026 .
    'Auu____1026 ->
      FStar_Range.range -> 'Auu____1026 FStar_Syntax_Syntax.syntax
  =
  fun t  -> fun r  -> FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None r 
let set_memo :
  'a . FStar_TypeChecker_Cfg.cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit
  =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.FStar_TypeChecker_Cfg.memoize_lazy
        then
          let uu____1069 = FStar_ST.op_Bang r  in
          match uu____1069 with
          | FStar_Pervasives_Native.Some uu____1095 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (closure_to_string : closure -> Prims.string) =
  fun uu___1_1128  ->
    match uu___1_1128 with
    | Clos (env,t,uu____1132,uu____1133) ->
        let uu____1180 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____1190 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1180 uu____1190
    | Univ uu____1193 -> "Univ"
    | Dummy  -> "dummy"
  
let (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____1219 =
      FStar_List.map
        (fun uu____1235  ->
           match uu____1235 with
           | (bopt,c) ->
               let uu____1249 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____1254 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____1249 uu____1254) env
       in
    FStar_All.pipe_right uu____1219 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___2_1268  ->
    match uu___2_1268 with
    | Arg (c,uu____1271,uu____1272) ->
        let uu____1273 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1273
    | MemoLazy uu____1276 -> "MemoLazy"
    | Abs (uu____1284,bs,uu____1286,uu____1287,uu____1288) ->
        let uu____1293 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1293
    | UnivArgs uu____1304 -> "UnivArgs"
    | Match uu____1312 -> "Match"
    | App (uu____1322,t,uu____1324,uu____1325) ->
        let uu____1326 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1326
    | CBVApp (uu____1329,t,uu____1331,uu____1332) ->
        let uu____1333 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "CBVApp %s" uu____1333
    | Meta (uu____1336,m,uu____1338) -> "Meta"
    | Let uu____1340 -> "Let"
    | Cfg uu____1350 -> "Cfg"
    | Debug (t,uu____1353) ->
        let uu____1354 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1354
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1368 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1368 (FStar_String.concat "; ")
  
let is_empty : 'Auu____1383 . 'Auu____1383 Prims.list -> Prims.bool =
  fun uu___3_1391  ->
    match uu___3_1391 with | [] -> true | uu____1395 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___121_1428  ->
           match () with
           | () ->
               let uu____1429 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1429) ()
      with
      | uu___120_1446 ->
          let uu____1447 =
            let uu____1449 = FStar_Syntax_Print.db_to_string x  in
            let uu____1451 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1449
              uu____1451
             in
          failwith uu____1447
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____1462 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____1462
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1469 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____1469
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1476 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____1476
          then
            FStar_Pervasives_Native.Some FStar_Parser_Const.effect_PURE_lid
          else FStar_Pervasives_Native.None))
  
let (norm_universe :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun cfg  ->
    fun env  ->
      fun u  ->
        let norm_univs us =
          let us1 = FStar_Util.sort_with FStar_Syntax_Util.compare_univs us
             in
          let uu____1514 =
            FStar_List.fold_left
              (fun uu____1540  ->
                 fun u1  ->
                   match uu____1540 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1565 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1565 with
                        | (k_u,n1) ->
                            let uu____1583 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1583
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1514 with
          | (uu____1604,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___155_1630  ->
                    match () with
                    | () ->
                        let uu____1633 =
                          let uu____1634 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____1634  in
                        (match uu____1633 with
                         | Univ u3 ->
                             ((let uu____1653 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____1653
                               then
                                 let uu____1658 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1658
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____1663 ->
                             let uu____1664 =
                               let uu____1666 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1666
                                in
                             failwith uu____1664)) ()
               with
               | uu____1676 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1682 =
                        let uu____1684 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____1684
                         in
                      failwith uu____1682))
          | FStar_Syntax_Syntax.U_unif uu____1689 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1698 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1707 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1714 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1714 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1731 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1731 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1742 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1752 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1752 with
                                  | (uu____1759,m) -> n1 <= m))
                           in
                        if uu____1742 then rest1 else us1
                    | uu____1768 -> us1)
               | uu____1774 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1778 = aux u3  in
              FStar_List.map (fun _1781  -> FStar_Syntax_Syntax.U_succ _1781)
                uu____1778
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1785 = aux u  in
           match uu____1785 with
           | [] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::[] -> FStar_Syntax_Syntax.U_zero
           | (FStar_Syntax_Syntax.U_zero )::u1::[] -> u1
           | (FStar_Syntax_Syntax.U_zero )::us ->
               FStar_Syntax_Syntax.U_max us
           | u1::[] -> u1
           | us -> FStar_Syntax_Syntax.U_max us)
  
let rec (inline_closure_env :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____1946  ->
               let uu____1947 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1949 = env_to_string env  in
               let uu____1951 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 ">>> %s (env=%s)\nClosure_as_term %s\n"
                 uu____1947 uu____1949 uu____1951);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____1964 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1967 ->
                    let uu____1982 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____1982
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____1983 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____1984 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____1985 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____1986 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____2011 ->
                           let uu____2024 =
                             let uu____2026 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____2028 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____2026 uu____2028
                              in
                           failwith uu____2024
                       | uu____2033 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_2069  ->
                                         match uu___4_2069 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____2076 =
                                               let uu____2083 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____2083)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____2076
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___249_2095 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___249_2095.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___249_2095.FStar_Syntax_Syntax.sort)
                                                  })
                                                in
                                             let t1 =
                                               inline_closure_env cfg env []
                                                 x_i
                                                in
                                             (match t1.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_bvar
                                                  x_j ->
                                                  FStar_Syntax_Syntax.NM
                                                    (x,
                                                      (x_j.FStar_Syntax_Syntax.index))
                                              | uu____2101 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____2104 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___258_2109 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___258_2109.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___258_2109.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____2130 =
                        let uu____2131 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____2131  in
                      mk uu____2130 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____2139 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2139  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____2141 = lookup_bvar env x  in
                    (match uu____2141 with
                     | Univ uu____2144 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___274_2149 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___274_2149.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___274_2149.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____2155,uu____2156) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____2247  ->
                              fun stack1  ->
                                match uu____2247 with
                                | (a,aq) ->
                                    let uu____2259 =
                                      let uu____2260 =
                                        let uu____2267 =
                                          let uu____2268 =
                                            let uu____2300 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____2300, false)  in
                                          Clos uu____2268  in
                                        (uu____2267, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2260  in
                                    uu____2259 :: stack1) args)
                       in
                    inline_closure_env cfg env stack1 head1
                | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                    let env' =
                      FStar_All.pipe_right env
                        (FStar_List.fold_right
                           (fun _b  ->
                              fun env1  ->
                                (FStar_Pervasives_Native.None, Dummy) :: env1)
                           bs)
                       in
                    let stack1 =
                      (Abs (env, bs, env', lopt, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env' stack1 body
                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                    let uu____2468 = close_binders cfg env bs  in
                    (match uu____2468 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____2518) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env stack
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2529 =
                      let uu____2542 =
                        let uu____2551 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2551]  in
                      close_binders cfg env uu____2542  in
                    (match uu____2529 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____2596 =
                             let uu____2597 =
                               let uu____2604 =
                                 let uu____2605 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2605
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2604, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2597  in
                           mk uu____2596 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2704 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____2704
                      | FStar_Util.Inr c ->
                          let uu____2718 = close_comp cfg env c  in
                          FStar_Util.Inr uu____2718
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____2737 =
                        let uu____2738 =
                          let uu____2765 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____2765, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2738  in
                      mk uu____2737 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2811 =
                            let uu____2812 =
                              let uu____2819 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____2819, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2812  in
                          mk uu____2811 t.FStar_Syntax_Syntax.pos
                      | FStar_Syntax_Syntax.Quote_static  ->
                          let qi1 =
                            FStar_Syntax_Syntax.on_antiquoted
                              (non_tail_inline_closure_env cfg env) qi
                             in
                          mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                            t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                    let stack1 = (Meta (env, m, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env stack1 t'
                | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                    let env0 = env  in
                    let env1 =
                      FStar_List.fold_left
                        (fun env1  -> fun uu____2874  -> dummy :: env1) env
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    let typ =
                      non_tail_inline_closure_env cfg env1
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let def =
                      non_tail_inline_closure_env cfg env1
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    let uu____2895 =
                      let uu____2906 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2906
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2928 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___366_2944 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___366_2944.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___366_2944.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2928))
                       in
                    (match uu____2895 with
                     | (nm,body1) ->
                         let attrs =
                           FStar_List.map
                             (non_tail_inline_closure_env cfg env0)
                             lb.FStar_Syntax_Syntax.lbattrs
                            in
                         let lb1 =
                           let uu___372_2971 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___372_2971.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___372_2971.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs = attrs;
                             FStar_Syntax_Syntax.lbpos =
                               (uu___372_2971.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2988,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____3054  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____3071 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____3071
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____3086  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____3110 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____3110
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___395_3121 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___395_3121.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___395_3121.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___398_3122 = lb  in
                      let uu____3123 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___398_3122.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___398_3122.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____3123;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___398_3122.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___398_3122.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____3155  -> fun env1  -> dummy :: env1)
                          lbs1 env
                         in
                      non_tail_inline_closure_env cfg body_env body  in
                    let t1 =
                      mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                        t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
                    let stack1 =
                      (Match
                         (env, branches, cfg, (t.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    inline_closure_env cfg env stack1 head1))

and (non_tail_inline_closure_env :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun cfg  -> fun env  -> fun t  -> inline_closure_env cfg env [] t

and (rebuild_closure :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____3247  ->
               let uu____3248 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3250 = env_to_string env  in
               let uu____3252 = stack_to_string stack  in
               let uu____3254 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 ">>> %s (env=%s, stack=%s)\nRebuild closure_as_term %s\n"
                 uu____3248 uu____3250 uu____3252 uu____3254);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3261,uu____3262),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (CBVApp (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____3357 = close_binders cfg env' bs  in
               (match uu____3357 with
                | (bs1,uu____3373) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3393 =
                      let uu___465_3396 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___465_3396.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___465_3396.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____3393)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____3452 =
                 match uu____3452 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3567 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3598 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3687  ->
                                     fun uu____3688  ->
                                       match (uu____3687, uu____3688) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____3838 = norm_pat env4 p1
                                              in
                                           (match uu____3838 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____3598 with
                            | (pats1,env4) ->
                                ((let uu___502_4008 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___502_4008.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___506_4029 = x  in
                             let uu____4030 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___506_4029.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___506_4029.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4030
                             }  in
                           ((let uu___509_4044 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___509_4044.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___513_4055 = x  in
                             let uu____4056 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___513_4055.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___513_4055.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4056
                             }  in
                           ((let uu___516_4070 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___516_4070.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___522_4086 = x  in
                             let uu____4087 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___522_4086.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___522_4086.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4087
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___526_4104 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___526_4104.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____4109 = norm_pat env2 pat  in
                     (match uu____4109 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____4178 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____4178
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____4197 =
                   let uu____4198 =
                     let uu____4221 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____4221)  in
                   FStar_Syntax_Syntax.Tm_match uu____4198  in
                 mk uu____4197 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
                     let uu____4357 =
                       let uu____4378 =
                         FStar_All.pipe_right names1
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m))
                          in
                       let uu____4395 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1  ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4504  ->
                                         match uu____4504 with
                                         | (a,q) ->
                                             let uu____4531 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a
                                                in
                                             (uu____4531, q)))))
                          in
                       (uu____4378, uu____4395)  in
                     FStar_Syntax_Syntax.Meta_pattern uu____4357
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4560 =
                       let uu____4567 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4567)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4560
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4579 =
                       let uu____4588 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4588)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4579
                 | uu____4593 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____4599 -> failwith "Impossible: unexpected stack element")

and (close_imp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun imp  ->
        match imp with
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
            let uu____4615 =
              let uu____4616 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____4616  in
            FStar_Pervasives_Native.Some uu____4615
        | i -> i

and (close_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) Prims.list * env))
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____4633 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4717  ->
                  fun uu____4718  ->
                    match (uu____4717, uu____4718) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___581_4858 = b  in
                          let uu____4859 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___581_4858.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___581_4858.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4859
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____4633 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

and (close_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env  ->
      fun c  ->
        match env with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
            -> c
        | uu____5001 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5014 = inline_closure_env cfg env [] t  in
                 let uu____5015 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5014 uu____5015
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5028 = inline_closure_env cfg env [] t  in
                 let uu____5029 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5028 uu____5029
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5083  ->
                           match uu____5083 with
                           | (a,q) ->
                               let uu____5104 =
                                 inline_closure_env cfg env [] a  in
                               (uu____5104, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_5121  ->
                           match uu___5_5121 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5125 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5125
                           | f -> f))
                    in
                 let uu____5129 =
                   let uu___614_5130 = c1  in
                   let uu____5131 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5131;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___614_5130.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5129)

and (close_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___6_5149  ->
                      match uu___6_5149 with
                      | FStar_Syntax_Syntax.DECREASES uu____5151 -> false
                      | uu____5155 -> true))
               in
            let rc1 =
              let uu___626_5158 = rc  in
              let uu____5159 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___626_5158.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5159;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5168 -> lopt

let (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___7_5189  ->
            match uu___7_5189 with
            | FStar_Syntax_Syntax.DECREASES uu____5191 -> false
            | uu____5195 -> true))
  
let (closure_as_term :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun cfg  -> fun env  -> fun t  -> non_tail_inline_closure_env cfg env t 
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____5242 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____5242 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5281 = FStar_Syntax_Embeddings.unembed e t  in
        uu____5281 false FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____5301 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____5301) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____5363  ->
           fun subst1  ->
             match uu____5363 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____5404,uu____5405)) ->
                      let uu____5466 = b  in
                      (match uu____5466 with
                       | (bv,uu____5474) ->
                           let uu____5475 =
                             let uu____5477 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5477  in
                           if uu____5475
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____5485 = unembed_binder term1  in
                              match uu____5485 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5492 =
                                      let uu___666_5493 = bv  in
                                      let uu____5494 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___666_5493.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___666_5493.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5494
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5492
                                     in
                                  let b_for_x =
                                    let uu____5500 =
                                      let uu____5507 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5507)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5500  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___8_5523  ->
                                         match uu___8_5523 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5525,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5527;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5528;_})
                                             ->
                                             let uu____5533 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5533
                                         | uu____5535 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____5537 -> subst1)) env []
  
let reduce_primops :
  'Auu____5559 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5559)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun env  ->
        fun tm  ->
          if
            Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
          then tm
          else
            (let uu____5611 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5611 with
             | (head1,args) ->
                 let uu____5656 =
                   let uu____5657 = FStar_Syntax_Util.un_uinst head1  in
                   uu____5657.FStar_Syntax_Syntax.n  in
                 (match uu____5656 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5663 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5663 with
                       | FStar_Pervasives_Native.Some prim_step when
                           prim_step.FStar_TypeChecker_Cfg.strong_reduction_ok
                             ||
                             (Prims.op_Negation
                                cfg.FStar_TypeChecker_Cfg.strong)
                           ->
                           let l = FStar_List.length args  in
                           if l < prim_step.FStar_TypeChecker_Cfg.arity
                           then
                             (FStar_TypeChecker_Cfg.log_primops cfg
                                (fun uu____5686  ->
                                   let uu____5687 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5689 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5691 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5687 uu____5689 uu____5691);
                              tm)
                           else
                             (let uu____5696 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5696 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5782  ->
                                        let uu____5783 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5783);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5788  ->
                                             if
                                               prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                                             then mk_psc_subst cfg env
                                             else [])
                                      }  in
                                    let r =
                                      prim_step.FStar_TypeChecker_Cfg.interpretation
                                        psc norm_cb args_1
                                       in
                                    match r with
                                    | FStar_Pervasives_Native.None  ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5802  ->
                                              let uu____5803 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5803);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5811  ->
                                              let uu____5812 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5814 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5812 uu____5814);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5817 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5821  ->
                                 let uu____5822 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5822);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5828  ->
                            let uu____5829 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5829);
                       (match args with
                        | (a1,uu____5835)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5860 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5874  ->
                            let uu____5875 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5875);
                       (match args with
                        | (t,uu____5881)::(r,uu____5883)::[] ->
                            let uu____5924 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5924 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5930 -> tm))
                  | uu____5941 -> tm))
  
let reduce_equality :
  'Auu____5952 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5952)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___754_6001 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___756_6004 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___756_6004.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___756_6004.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___756_6004.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.zeta_full =
                    (uu___756_6004.FStar_TypeChecker_Cfg.zeta_full);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___756_6004.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___756_6004.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___756_6004.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___756_6004.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___756_6004.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___756_6004.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___756_6004.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___756_6004.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___756_6004.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___756_6004.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___756_6004.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___756_6004.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___756_6004.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___756_6004.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___756_6004.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___756_6004.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___756_6004.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___756_6004.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___756_6004.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___756_6004.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___756_6004.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___756_6004.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___754_6001.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___754_6001.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___754_6001.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___754_6001.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___754_6001.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___754_6001.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___754_6001.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____6015 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____6026 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____6037 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____6058 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____6058
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____6090 =
        let uu____6091 = FStar_Syntax_Util.un_uinst hd1  in
        uu____6091.FStar_Syntax_Syntax.n  in
      match uu____6090 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu____6100 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____6109 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____6109)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____6122 =
        let uu____6123 = FStar_Syntax_Util.un_uinst hd1  in
        uu____6123.FStar_Syntax_Syntax.n  in
      match uu____6122 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6181 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____6181 rest
           | uu____6208 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6248 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____6248 rest
           | uu____6267 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____6341 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____6341 rest
           | uu____6376 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6378 ->
          let uu____6379 =
            let uu____6381 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6381
             in
          failwith uu____6379
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6402  ->
    match uu___9_6402 with
    | FStar_Syntax_Embeddings.Zeta  -> [FStar_TypeChecker_Env.Zeta]
    | FStar_Syntax_Embeddings.ZetaFull  -> [FStar_TypeChecker_Env.ZetaFull]
    | FStar_Syntax_Embeddings.Iota  -> [FStar_TypeChecker_Env.Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [FStar_TypeChecker_Env.Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [FStar_TypeChecker_Env.Weak]
    | FStar_Syntax_Embeddings.HNF  -> [FStar_TypeChecker_Env.HNF]
    | FStar_Syntax_Embeddings.Primops  -> [FStar_TypeChecker_Env.Primops]
    | FStar_Syntax_Embeddings.Reify  -> [FStar_TypeChecker_Env.Reify]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____6409 =
          let uu____6412 =
            let uu____6413 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6413  in
          [uu____6412]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6409
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____6421 =
          let uu____6424 =
            let uu____6425 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____6425  in
          [uu____6424]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6421
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____6433 =
          let uu____6436 =
            let uu____6437 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6437  in
          [uu____6436]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6433
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s  ->
    let s1 = FStar_List.concatMap tr_norm_step s  in
    let add_exclude s2 z =
      let uu____6473 =
        FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2  in
      if uu____6473 then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2  in
    let s2 = FStar_TypeChecker_Env.Beta :: s1  in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta  in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota  in s4
  
let get_norm_request :
  'Auu____6498 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____6498) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6549 =
            let uu____6554 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6554 s  in
          match uu____6549 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6570 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6570
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None  in
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
                else []))
           in
        match args with
        | uu____6605::(tm,uu____6607)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (tm,uu____6636)::[] ->
            let s =
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.Zeta;
              FStar_TypeChecker_Env.Iota;
              FStar_TypeChecker_Env.Primops;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.Reify]  in
            FStar_Pervasives_Native.Some
              ((FStar_List.append inherited_steps s), tm)
        | (steps,uu____6657)::uu____6658::(tm,uu____6660)::[] ->
            let uu____6681 =
              let uu____6686 = full_norm steps  in parse_steps uu____6686  in
            (match uu____6681 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s), tm))
        | uu____6716 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6748 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6755  ->
                    match uu___10_6755 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6757 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6759 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6763 -> true
                    | uu____6767 -> false))
             in
          if uu____6748
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6777  ->
             let uu____6778 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6778);
        (let tm_norm =
           let uu____6782 =
             let uu____6797 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6797.FStar_TypeChecker_Env.nbe  in
           uu____6782 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6801  ->
              let uu____6802 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6802);
         tm_norm)
  
let firstn :
  'Auu____6812 .
    Prims.int ->
      'Auu____6812 Prims.list ->
        ('Auu____6812 Prims.list * 'Auu____6812 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___11_6869 =
        match uu___11_6869 with
        | (MemoLazy uu____6874)::s -> drop_irrel s
        | (UnivArgs uu____6884)::s -> drop_irrel s
        | s -> s  in
      let uu____6897 = drop_irrel stack  in
      match uu____6897 with
      | (App
          (uu____6901,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6902;
                        FStar_Syntax_Syntax.vars = uu____6903;_},uu____6904,uu____6905))::uu____6906
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6911 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6940) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6950) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6971  ->
                  match uu____6971 with
                  | (a,uu____6982) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6993 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____7010 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____7012 -> false
    | FStar_Syntax_Syntax.Tm_type uu____7026 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____7028 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____7030 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____7032 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____7034 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____7037 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____7045 -> false
    | FStar_Syntax_Syntax.Tm_let uu____7053 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____7068 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____7088 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____7104 -> true
    | FStar_Syntax_Syntax.Tm_match uu____7112 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7184  ->
                   match uu____7184 with
                   | (a,uu____7195) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7206) ->
        ((maybe_weakly_reduced t1) ||
           (match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> maybe_weakly_reduced t2
            | FStar_Util.Inr c2 -> aux_comp c2))
          ||
          ((match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> false
            | FStar_Pervasives_Native.Some tac -> maybe_weakly_reduced tac))
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        (maybe_weakly_reduced t1) ||
          ((match m with
            | FStar_Syntax_Syntax.Meta_pattern (uu____7305,args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7360  ->
                        match uu____7360 with
                        | (a,uu____7371) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7380,uu____7381,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7387,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7393 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7403 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7405 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7416 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7427 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7438 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7449 -> false
  
let (should_unfold :
  FStar_TypeChecker_Cfg.cfg ->
    (FStar_TypeChecker_Cfg.cfg -> Prims.bool) ->
      FStar_Syntax_Syntax.fv ->
        FStar_TypeChecker_Env.qninfo -> should_unfold_res)
  =
  fun cfg  ->
    fun should_reify1  ->
      fun fv  ->
        fun qninfo  ->
          let attrs =
            let uu____7482 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7482 with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some ats -> ats  in
          let yes = (true, false, false)  in
          let no = (false, false, false)  in
          let fully = (true, true, false)  in
          let reif = (true, false, true)  in
          let yesno b = if b then yes else no  in
          let fullyno b = if b then fully else no  in
          let comb_or l =
            FStar_List.fold_right
              (fun uu____7681  ->
                 fun uu____7682  ->
                   match (uu____7681, uu____7682) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7788 =
            match uu____7788 with
            | (x,y,z) ->
                let uu____7808 = FStar_Util.string_of_bool x  in
                let uu____7810 = FStar_Util.string_of_bool y  in
                let uu____7812 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7808 uu____7810
                  uu____7812
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7840  ->
                    let uu____7841 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7843 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7841 uu____7843);
               if b then reif else no)
            else
              if
                (let uu____7858 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7858)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7863  ->
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
                          ((is_rec,uu____7898),uu____7899);
                        FStar_Syntax_Syntax.sigrng = uu____7900;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7902;
                        FStar_Syntax_Syntax.sigattrs = uu____7903;
                        FStar_Syntax_Syntax.sigopts = uu____7904;_},uu____7905),uu____7906),uu____7907,uu____7908,uu____7909)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8018  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____8020,uu____8021,uu____8022,uu____8023) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8090  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____8093),uu____8094);
                        FStar_Syntax_Syntax.sigrng = uu____8095;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____8097;
                        FStar_Syntax_Syntax.sigattrs = uu____8098;
                        FStar_Syntax_Syntax.sigopts = uu____8099;_},uu____8100),uu____8101),uu____8102,uu____8103,uu____8104)
                     when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8213  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8215,FStar_Pervasives_Native.Some
                    uu____8216,uu____8217,uu____8218) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8286  ->
                           let uu____8287 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8287);
                      (let uu____8290 =
                         let uu____8302 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8328 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8328
                            in
                         let uu____8340 =
                           let uu____8352 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8378 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8378
                              in
                           let uu____8394 =
                             let uu____8406 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8432 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8432
                                in
                             [uu____8406]  in
                           uu____8352 :: uu____8394  in
                         uu____8302 :: uu____8340  in
                       comb_or uu____8290))
                 | (uu____8480,uu____8481,FStar_Pervasives_Native.Some
                    uu____8482,uu____8483) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8551  ->
                           let uu____8552 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8552);
                      (let uu____8555 =
                         let uu____8567 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8593 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8593
                            in
                         let uu____8605 =
                           let uu____8617 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8643 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8643
                              in
                           let uu____8659 =
                             let uu____8671 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8697 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8697
                                in
                             [uu____8671]  in
                           uu____8617 :: uu____8659  in
                         uu____8567 :: uu____8605  in
                       comb_or uu____8555))
                 | (uu____8745,uu____8746,uu____8747,FStar_Pervasives_Native.Some
                    uu____8748) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8816  ->
                           let uu____8817 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8817);
                      (let uu____8820 =
                         let uu____8832 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8858 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8858
                            in
                         let uu____8870 =
                           let uu____8882 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8908 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8908
                              in
                           let uu____8924 =
                             let uu____8936 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8962 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8962
                                in
                             [uu____8936]  in
                           uu____8882 :: uu____8924  in
                         uu____8832 :: uu____8870  in
                       comb_or uu____8820))
                 | uu____9010 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____9056  ->
                           let uu____9057 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____9059 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____9061 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____9057 uu____9059 uu____9061);
                      (let uu____9064 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_9070  ->
                                 match uu___12_9070 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____9076 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____9076 l))
                          in
                       FStar_All.pipe_left yesno uu____9064)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____9092  ->
               let uu____9093 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____9095 =
                 let uu____9097 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____9097  in
               let uu____9098 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____9093 uu____9095 uu____9098);
          (match res with
           | (false ,uu____9101,uu____9102) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____9127 ->
               let uu____9137 =
                 let uu____9139 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9139
                  in
               FStar_All.pipe_left failwith uu____9137)
  
let decide_unfolding :
  'Auu____9158 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____9158 ->
            FStar_Syntax_Syntax.fv ->
              FStar_TypeChecker_Env.qninfo ->
                (FStar_TypeChecker_Cfg.cfg * stack_elt Prims.list)
                  FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun rng  ->
          fun fv  ->
            fun qninfo  ->
              let res =
                should_unfold cfg (fun cfg1  -> should_reify cfg1 stack) fv
                  qninfo
                 in
              match res with
              | Should_unfold_no  -> FStar_Pervasives_Native.None
              | Should_unfold_yes  ->
                  FStar_Pervasives_Native.Some (cfg, stack)
              | Should_unfold_fully  ->
                  let cfg' =
                    let uu___1165_9227 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1167_9230 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1167_9230.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1167_9230.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1165_9227.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1165_9227.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1165_9227.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1165_9227.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1165_9227.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1165_9227.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1165_9227.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1165_9227.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' =
                    match stack with
                    | (UnivArgs (us,r))::stack' -> (UnivArgs (us, r)) ::
                        (Cfg cfg) :: stack'
                    | stack' -> (Cfg cfg) :: stack'  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let rec push1 e s =
                    match s with
                    | [] -> [e]
                    | (UnivArgs (us,r))::t ->
                        let uu____9292 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____9292
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9304 =
                      let uu____9311 =
                        let uu____9312 =
                          let uu____9313 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____9313  in
                        FStar_Syntax_Syntax.Tm_constant uu____9312  in
                      FStar_Syntax_Syntax.mk uu____9311  in
                    uu____9304 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let stack1 =
                    push1
                      (App
                         (env, ref, FStar_Pervasives_Native.None,
                           FStar_Range.dummyRange)) stack
                     in
                  FStar_Pervasives_Native.Some (cfg, stack1)
  
let (on_domain_lids : FStar_Ident.lident Prims.list) =
  let fext_lid s =
    FStar_Ident.lid_of_path ["FStar"; "FunctionalExtensionality"; s]
      FStar_Range.dummyRange
     in
  FStar_All.pipe_right ["on_domain"; "on_dom"; "on_domain_g"; "on_dom_g"]
    (FStar_List.map fext_lid)
  
let (is_fext_on_domain :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let is_on_dom fv =
      FStar_All.pipe_right on_domain_lids
        (FStar_List.existsb (fun l  -> FStar_Syntax_Syntax.fv_eq_lid fv l))
       in
    let uu____9379 =
      let uu____9380 = FStar_Syntax_Subst.compress t  in
      uu____9380.FStar_Syntax_Syntax.n  in
    match uu____9379 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9411 =
          let uu____9412 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9412.FStar_Syntax_Syntax.n  in
        (match uu____9411 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9429 =
                 let uu____9436 =
                   let uu____9447 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9447 FStar_List.tl  in
                 FStar_All.pipe_right uu____9436 FStar_List.hd  in
               FStar_All.pipe_right uu____9429 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9546 -> FStar_Pervasives_Native.None)
    | uu____9547 -> FStar_Pervasives_Native.None
  
let rec (norm :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          let t1 =
            if
              (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____9826 ->
                   let uu____9841 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9841
               | uu____9844 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9854  ->
               let uu____9855 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9857 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9859 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9861 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9869 =
                 let uu____9871 =
                   let uu____9874 = firstn (Prims.of_int (4)) stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9874
                    in
                 stack_to_string uu____9871  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9855 uu____9857 uu____9859 uu____9861 uu____9869);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9902  ->
               let uu____9903 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9903);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9909  ->
                     let uu____9910 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9910);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9913 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9917  ->
                     let uu____9918 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9918);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____9921 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9925  ->
                     let uu____9926 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9926);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9929 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9933  ->
                     let uu____9934 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9934);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9937;
                 FStar_Syntax_Syntax.fv_delta = uu____9938;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9942  ->
                     let uu____9943 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9943);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9946;
                 FStar_Syntax_Syntax.fv_delta = uu____9947;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9948);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9958  ->
                     let uu____9959 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9959);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____9965 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____9965 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _9968) when
                    _9968 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9972  ->
                          let uu____9973 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9973);
                     rebuild cfg env stack t1)
                | uu____9976 ->
                    let uu____9979 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____9979 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
               let qi1 =
                 FStar_Syntax_Syntax.on_antiquoted (norm cfg env []) qi  in
               let t2 =
                 mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                   t1.FStar_Syntax_Syntax.pos
                  in
               let uu____10018 = closure_as_term cfg env t2  in
               rebuild cfg env stack uu____10018
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10046 = is_norm_request hd1 args  in
                  uu____10046 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____10052 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____10052))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10080 = is_norm_request hd1 args  in
                  uu____10080 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1278_10087 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1280_10090 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1280_10090.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1278_10087.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1278_10087.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1278_10087.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1278_10087.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1278_10087.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1278_10087.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____10097 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____10097 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____10133  ->
                                 fun stack1  ->
                                   match uu____10133 with
                                   | (a,aq) ->
                                       let uu____10145 =
                                         let uu____10146 =
                                           let uu____10153 =
                                             let uu____10154 =
                                               let uu____10186 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____10186, false)
                                                in
                                             Clos uu____10154  in
                                           (uu____10153, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10146  in
                                       uu____10145 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10254  ->
                            let uu____10255 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10255);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     let tm' = closure_as_term cfg env tm  in
                     let start = FStar_Util.now ()  in
                     let tm_norm = nbe_eval cfg s tm'  in
                     let fin = FStar_Util.now ()  in
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let cfg'1 =
                           FStar_TypeChecker_Cfg.config' [] s
                             cfg.FStar_TypeChecker_Cfg.tcenv
                            in
                         let uu____10287 =
                           let uu____10289 =
                             let uu____10291 = FStar_Util.time_diff start fin
                                in
                             FStar_Pervasives_Native.snd uu____10291  in
                           FStar_Util.string_of_int uu____10289  in
                         let uu____10298 =
                           FStar_Syntax_Print.term_to_string tm'  in
                         let uu____10300 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                         let uu____10302 =
                           FStar_Syntax_Print.term_to_string tm_norm  in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____10287 uu____10298 uu____10300 uu____10302)
                      else ();
                      rebuild cfg env stack tm_norm)
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     let delta_level =
                       let uu____10322 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___13_10329  ->
                                 match uu___13_10329 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____10331 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____10333 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____10337 -> true
                                 | uu____10341 -> false))
                          in
                       if uu____10322
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let cfg'1 =
                       let uu___1318_10349 = cfg  in
                       let uu____10350 =
                         let uu___1320_10351 =
                           FStar_TypeChecker_Cfg.to_fsteps s  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1320_10351.FStar_TypeChecker_Cfg.for_extraction)
                         }  in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____10350;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1318_10349.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1318_10349.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1318_10349.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1318_10349.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1318_10349.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___1318_10349.FStar_TypeChecker_Cfg.reifying)
                       }  in
                     let stack' =
                       let tail1 = (Cfg cfg) :: stack  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____10359 =
                           let uu____10360 =
                             let uu____10365 = FStar_Util.now ()  in
                             (tm, uu____10365)  in
                           Debug uu____10360  in
                         uu____10359 :: tail1
                       else tail1  in
                     norm cfg'1 env stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10370 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10370
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10381 =
                      let uu____10388 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10388, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10381  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10397 = lookup_bvar env x  in
               (match uu____10397 with
                | Univ uu____10398 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      ((Prims.op_Negation fix) ||
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                        ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full
                    then
                      let uu____10452 = FStar_ST.op_Bang r  in
                      (match uu____10452 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10548  ->
                                 let uu____10549 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10551 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10549
                                   uu____10551);
                            (let uu____10554 = maybe_weakly_reduced t'  in
                             if uu____10554
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____10557 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10601)::uu____10602 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10613,uu____10614))::stack_rest ->
                    (match c with
                     | Univ uu____10618 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10627 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10657  ->
                                    let uu____10658 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10658);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10694  ->
                                    let uu____10695 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10695);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10739  ->
                          let uu____10740 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10740);
                     norm cfg env stack1 t1)
                | (Cfg uu____10743)::uu____10744 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10751 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10751 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10787  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10831 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10831)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_10839 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_10839.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_10839.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10840 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10846  ->
                                 let uu____10847 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10847);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1449_10862 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_10862.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_10862.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_10862.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_10862.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_10862.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_10862.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_10862.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_10862.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Match uu____10866)::uu____10867 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10882 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10882 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10918  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____10962 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10962)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_10970 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_10970.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_10970.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10971 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10977  ->
                                 let uu____10978 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10978);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1449_10993 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_10993.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_10993.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_10993.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_10993.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_10993.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_10993.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_10993.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_10993.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____10997)::uu____10998 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11009 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11009 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11045  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11089 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11089)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11097 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11097.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11097.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11098 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11104  ->
                                 let uu____11105 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11105);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1449_11120 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11120.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11120.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11120.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11120.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11120.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11120.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11120.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11120.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11124)::uu____11125 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11138 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11138 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11174  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11218 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11218)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11226 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11226.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11226.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11227 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11233  ->
                                 let uu____11234 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11234);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1449_11249 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11249.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11249.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11249.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11249.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11249.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11249.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11249.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11249.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11253)::uu____11254 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11269 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11269 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11305  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11349 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11349)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11357 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11357.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11357.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11358 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11364  ->
                                 let uu____11365 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11365);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1449_11380 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11380.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11380.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11380.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11380.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11380.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11380.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11380.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11380.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11384)::uu____11385 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11400 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11400 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11436  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11480 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11480)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11488 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11488.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11488.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11489 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11495  ->
                                 let uu____11496 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11496);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1449_11511 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11511.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11511.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11511.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11511.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11511.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11511.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11511.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11511.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (CBVApp uu____11515)::uu____11516 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11531 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11531 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11567  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11611 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11611)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11619 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11619.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11619.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11620 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11626  ->
                                 let uu____11627 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11627);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1449_11642 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11642.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11642.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11642.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11642.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11642.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11642.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11642.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11642.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11646)::uu____11647 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11666 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11666 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11702  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11746 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11746)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11754 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11754.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11754.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11755 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11761  ->
                                 let uu____11762 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11762);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1449_11777 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11777.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11777.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11777.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11777.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11777.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11777.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11777.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11777.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | [] ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11785 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11785 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11821  -> dummy :: env1) env)
                              in
                           let lopt1 =
                             match lopt with
                             | FStar_Pervasives_Native.Some rc ->
                                 let rct =
                                   if
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                                   then
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (fun t2  ->
                                          let uu____11865 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11865)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11873 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11873.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11873.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11874 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11880  ->
                                 let uu____11881 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11881);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1449_11896 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11896.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11896.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11896.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11896.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11896.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11896.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11896.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11896.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let strict_args =
                 let uu____11932 =
                   let uu____11933 = FStar_Syntax_Util.un_uinst head1  in
                   uu____11933.FStar_Syntax_Syntax.n  in
                 match uu____11932 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11942 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11963  ->
                              fun stack1  ->
                                match uu____11963 with
                                | (a,aq) ->
                                    let uu____11975 =
                                      let uu____11976 =
                                        let uu____11983 =
                                          let uu____11984 =
                                            let uu____12016 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____12016, false)  in
                                          Clos uu____11984  in
                                        (uu____11983, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11976  in
                                    uu____11975 :: stack1) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12084  ->
                          let uu____12085 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12085);
                     norm cfg env stack1 head1)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____12136  ->
                              match uu____12136 with
                              | (a,i) ->
                                  let uu____12147 = norm cfg env [] a  in
                                  (uu____12147, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____12153 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____12168 = FStar_List.nth norm_args i
                                    in
                                 match uu____12168 with
                                 | (arg_i,uu____12179) ->
                                     let uu____12180 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____12180 with
                                      | (head2,uu____12199) ->
                                          let uu____12224 =
                                            let uu____12225 =
                                              FStar_Syntax_Util.un_uinst
                                                head2
                                               in
                                            uu____12225.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____12224 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____12229 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____12232 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____12232
                                           | uu____12233 -> false)))))
                       in
                    if uu____12153
                    then
                      let stack1 =
                        FStar_All.pipe_right stack
                          (FStar_List.fold_right
                             (fun uu____12250  ->
                                fun stack1  ->
                                  match uu____12250 with
                                  | (a,aq) ->
                                      let uu____12262 =
                                        let uu____12263 =
                                          let uu____12270 =
                                            let uu____12271 =
                                              let uu____12303 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env, a, uu____12303, false)
                                               in
                                            Clos uu____12271  in
                                          (uu____12270, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____12263  in
                                      uu____12262 :: stack1) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12385  ->
                            let uu____12386 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12386);
                       norm cfg env stack1 head1)
                    else
                      (let head2 = closure_as_term cfg env head1  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                           FStar_Pervasives_Native.None
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env stack term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12406) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
               -> norm cfg env stack x.FStar_Syntax_Syntax.sort
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 (match (env, stack) with
                  | ([],[]) ->
                      let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort
                         in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___1511_12451 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1511_12451.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1511_12451.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12452 ->
                      let uu____12467 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12467)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12471 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12471 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12502 =
                          let uu____12503 =
                            let uu____12510 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1520_12516 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1520_12516.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1520_12516.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12510)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12503  in
                        mk uu____12502 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12540 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12540
               else
                 (let uu____12543 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12543 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12551 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12577  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12551 c1  in
                      let t2 =
                        let uu____12601 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12601 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12714)::uu____12715 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12728  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12730)::uu____12731 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12742  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12744,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12745;
                                   FStar_Syntax_Syntax.vars = uu____12746;_},uu____12747,uu____12748))::uu____12749
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12756  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12758)::uu____12759 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12770  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12772 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12775  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12780  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12806 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12806
                         | FStar_Util.Inr c ->
                             let uu____12820 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12820
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12843 =
                               let uu____12844 =
                                 let uu____12871 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12871, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12844
                                in
                             mk uu____12843 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12906 ->
                           let uu____12907 =
                             let uu____12908 =
                               let uu____12909 =
                                 let uu____12936 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12936, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12909
                                in
                             mk uu____12908 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12907))))
           | FStar_Syntax_Syntax.Tm_match (head1,branches) ->
               let stack1 =
                 (Match (env, branches, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack  in
               if
                 ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    &&
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weakly_reduce_scrutinee)
                   &&
                   (Prims.op_Negation
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak)
               then
                 let cfg' =
                   let uu___1599_13014 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1601_13017 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1601_13017.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1599_13014.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1599_13014.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1599_13014.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1599_13014.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1599_13014.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1599_13014.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1599_13014.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1599_13014.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 norm cfg' env ((Cfg cfg) :: stack1) head1
               else norm cfg env stack1 head1
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____13058 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____13058 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1614_13078 = cfg  in
                               let uu____13079 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1614_13078.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____13079;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1614_13078.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1614_13078.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1614_13078.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1614_13078.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1614_13078.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1614_13078.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1614_13078.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____13086 =
                                 let uu____13087 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____13087  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13086
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1621_13090 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1621_13090.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1621_13090.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1621_13090.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1621_13090.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____13091 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____13091
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13104,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13105;
                               FStar_Syntax_Syntax.lbunivs = uu____13106;
                               FStar_Syntax_Syntax.lbtyp = uu____13107;
                               FStar_Syntax_Syntax.lbeff = uu____13108;
                               FStar_Syntax_Syntax.lbdef = uu____13109;
                               FStar_Syntax_Syntax.lbattrs = uu____13110;
                               FStar_Syntax_Syntax.lbpos = uu____13111;_}::uu____13112),uu____13113)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let uu____13158 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
               if uu____13158
               then
                 let binder =
                   let uu____13162 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13162  in
                 let env1 =
                   let uu____13172 =
                     let uu____13179 =
                       let uu____13180 =
                         let uu____13212 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13212,
                           false)
                          in
                       Clos uu____13180  in
                     ((FStar_Pervasives_Native.Some binder), uu____13179)  in
                   uu____13172 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____13287  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13291 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu____13294 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff
                          in
                       FStar_Syntax_Util.is_div_effect uu____13294)
                     in
                  if uu____13291
                  then
                    let ffun =
                      let uu____13299 =
                        let uu____13306 =
                          let uu____13307 =
                            let uu____13326 =
                              let uu____13335 =
                                let uu____13342 =
                                  FStar_All.pipe_right
                                    lb.FStar_Syntax_Syntax.lbname
                                    FStar_Util.left
                                   in
                                FStar_Syntax_Syntax.mk_binder uu____13342  in
                              [uu____13335]  in
                            (uu____13326, body, FStar_Pervasives_Native.None)
                             in
                          FStar_Syntax_Syntax.Tm_abs uu____13307  in
                        FStar_Syntax_Syntax.mk uu____13306  in
                      uu____13299 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    let stack1 =
                      (CBVApp
                         (env, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____13376  ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env stack1 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____13383  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____13385 = closure_as_term cfg env t1  in
                        rebuild cfg env stack uu____13385))
                    else
                      (let uu____13388 =
                         let uu____13393 =
                           let uu____13394 =
                             let uu____13401 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____13401
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____13394]  in
                         FStar_Syntax_Subst.open_term uu____13393 body  in
                       match uu____13388 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____13428  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____13437 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____13437  in
                               FStar_Util.Inl
                                 (let uu___1667_13453 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1667_13453.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1667_13453.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____13456  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1672_13459 = lb  in
                                let uu____13460 =
                                  norm cfg env []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____13463 =
                                  FStar_List.map (norm cfg env [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1672_13459.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1672_13459.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____13460;
                                  FStar_Syntax_Syntax.lbattrs = uu____13463;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1672_13459.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____13498  -> dummy :: env1)
                                     env)
                                 in
                              let stack1 = (Cfg cfg) :: stack  in
                              let cfg1 =
                                let uu___1679_13523 = cfg  in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1679_13523.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1679_13523.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1679_13523.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1679_13523.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1679_13523.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1679_13523.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1679_13523.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1679_13523.FStar_TypeChecker_Cfg.reifying)
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____13527  ->
                                   FStar_Util.print_string
                                     "+++ Normalizing Tm_let -- body\n");
                              norm cfg1 env'
                                ((Let
                                    (env, bs, lb1,
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) body1)))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
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
               let uu____13548 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13548 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13584 =
                               let uu___1695_13585 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1695_13585.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1695_13585.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13584  in
                           let uu____13586 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13586 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13612 =
                                   FStar_List.map (fun uu____13634  -> dummy)
                                     xs1
                                    in
                                 let uu____13641 =
                                   let uu____13650 =
                                     FStar_List.map
                                       (fun uu____13666  -> dummy) lbs1
                                      in
                                   FStar_List.append uu____13650 env  in
                                 FStar_List.append uu____13612 uu____13641
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13686 =
                                       let uu___1709_13687 = rc  in
                                       let uu____13688 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1709_13687.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13688;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1709_13687.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13686
                                 | uu____13697 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1714_13703 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1714_13703.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1714_13703.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1714_13703.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1714_13703.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13713 =
                        FStar_List.map (fun uu____13729  -> dummy) lbs2  in
                      FStar_List.append uu____13713 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13737 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13737 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1723_13753 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1723_13753.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1723_13753.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu____13787 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13787
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13808 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13886  ->
                        match uu____13886 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1739_14011 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1739_14011.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1739_14011.FStar_Syntax_Syntax.sort)
                              }  in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv  in
                            let fix_f_i =
                              mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            let memo =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            let rec_env1 =
                              (FStar_Pervasives_Native.None,
                                (Clos (env, fix_f_i, memo, true)))
                              :: rec_env  in
                            (rec_env1, (memo :: memos), (i + Prims.int_one)))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], Prims.int_zero)
                  in
               (match uu____13808 with
                | (rec_env,memos,uu____14202) ->
                    let uu____14257 =
                      FStar_List.map2
                        (fun lb  ->
                           fun memo  ->
                             FStar_ST.op_Colon_Equals memo
                               (FStar_Pervasives_Native.Some
                                  (rec_env, (lb.FStar_Syntax_Syntax.lbdef))))
                        (FStar_Pervasives_Native.snd lbs) memos
                       in
                    let body_env =
                      FStar_List.fold_right
                        (fun lb  ->
                           fun env1  ->
                             let uu____14506 =
                               let uu____14513 =
                                 let uu____14514 =
                                   let uu____14546 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14546, false)
                                    in
                                 Clos uu____14514  in
                               (FStar_Pervasives_Native.None, uu____14513)
                                in
                             uu____14506 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14631  ->
                     let uu____14632 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14632);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14656 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14660::uu____14661 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14666) ->
                                 norm cfg env ((Meta (env, m, r)) :: stack)
                                   head1
                             | FStar_Syntax_Syntax.Meta_pattern (names1,args)
                                 ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 let names2 =
                                   FStar_All.pipe_right names1
                                     (FStar_List.map (norm cfg env []))
                                    in
                                 norm cfg env
                                   ((Meta
                                       (env,
                                         (FStar_Syntax_Syntax.Meta_pattern
                                            (names2, args1)),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____14745 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern
                                  (names1,args) ->
                                  let names2 =
                                    FStar_All.pipe_right names1
                                      (FStar_List.map (norm cfg env []))
                                     in
                                  let uu____14793 =
                                    let uu____14814 =
                                      norm_pattern_args cfg env args  in
                                    (names2, uu____14814)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14793
                              | uu____14843 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14849 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14865 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14879 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14893 =
                        let uu____14895 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14897 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14895 uu____14897
                         in
                      failwith uu____14893
                    else
                      (let uu____14902 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____14902)
                | uu____14903 -> norm cfg env stack t2))

and (do_unfold_fv :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t0  ->
          fun qninfo  ->
            fun f  ->
              let uu____14912 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14912 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14926  ->
                        let uu____14927 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14927);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14940  ->
                        let uu____14941 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14943 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14941 uu____14943);
                   (let t1 =
                      if
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_until
                          =
                          (FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.delta_constant)
                      then t
                      else
                        FStar_Syntax_Subst.set_use_range
                          t0.FStar_Syntax_Syntax.pos t
                       in
                    let n1 = FStar_List.length us  in
                    if n1 > Prims.int_zero
                    then
                      match stack with
                      | (UnivArgs (us',uu____14956))::stack1 ->
                          ((let uu____14965 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14965
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14973 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14973) us'
                            else ());
                           (let env1 =
                              FStar_All.pipe_right us'
                                (FStar_List.fold_left
                                   (fun env1  ->
                                      fun u  ->
                                        (FStar_Pervasives_Native.None,
                                          (Univ u))
                                        :: env1) env)
                               in
                            norm cfg env1 stack1 t1))
                      | uu____15009 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____15012 ->
                          let uu____15015 =
                            let uu____15017 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____15017
                             in
                          failwith uu____15015
                    else norm cfg env stack t1))

and (reduce_impure_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.monad_name,(FStar_Syntax_Syntax.monad_name *
                                            FStar_Syntax_Syntax.monad_name))
            FStar_Util.either ->
            FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun head1  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env [] t  in
              let uu____15037 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations
                then
                  let new_steps =
                    [FStar_TypeChecker_Env.PureSubtermsWithinComputations;
                    FStar_TypeChecker_Env.Primops;
                    FStar_TypeChecker_Env.AllowUnboundUniverses;
                    FStar_TypeChecker_Env.EraseUniverses;
                    FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                    FStar_TypeChecker_Env.Inlining]  in
                  let cfg' =
                    let uu___1850_15055 = cfg  in
                    let uu____15056 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps
                       in
                    {
                      FStar_TypeChecker_Cfg.steps = uu____15056;
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1850_15055.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1850_15055.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        [FStar_TypeChecker_Env.InliningDelta;
                        FStar_TypeChecker_Env.Eager_unfolding_only];
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1850_15055.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1850_15055.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1850_15055.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1850_15055.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1850_15055.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  (cfg', ((Cfg cfg) :: stack))
                else (cfg, stack)  in
              match uu____15037 with
              | (cfg1,stack1) ->
                  let metadata =
                    match m with
                    | FStar_Util.Inl m1 ->
                        FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                    | FStar_Util.Inr (m1,m') ->
                        FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1)
                     in
                  norm cfg1 env
                    ((Meta (env, metadata, (head1.FStar_Syntax_Syntax.pos)))
                    :: stack1) head1

and (do_reify_monadic :
  (unit -> FStar_Syntax_Syntax.term) ->
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.monad_name ->
              FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun fallback  ->
    fun cfg  ->
      fun env  ->
        fun stack  ->
          fun top  ->
            fun m  ->
              fun t  ->
                (match stack with
                 | (App
                     (uu____15097,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____15098;
                                    FStar_Syntax_Syntax.vars = uu____15099;_},uu____15100,uu____15101))::uu____15102
                     -> ()
                 | uu____15107 ->
                     let uu____15110 =
                       let uu____15112 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____15112
                        in
                     failwith uu____15110);
                (let top0 = top  in
                 let top1 = FStar_Syntax_Util.unascribe top  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____15121  ->
                      let uu____15122 = FStar_Syntax_Print.tag_of_term top1
                         in
                      let uu____15124 =
                        FStar_Syntax_Print.term_to_string top1  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____15122
                        uu____15124);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1  in
                  let uu____15128 =
                    let uu____15129 = FStar_Syntax_Subst.compress top2  in
                    uu____15129.FStar_Syntax_Syntax.n  in
                  match uu____15128 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m
                         in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name
                         in
                      let uu____15151 =
                        let uu____15160 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr
                           in
                        FStar_All.pipe_right uu____15160 FStar_Util.must  in
                      (match uu____15151 with
                       | (uu____15175,repr) ->
                           let uu____15185 =
                             let uu____15192 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr
                                in
                             FStar_All.pipe_right uu____15192 FStar_Util.must
                              in
                           (match uu____15185 with
                            | (uu____15229,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15235 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15246 =
                                         let uu____15247 =
                                           FStar_Syntax_Subst.compress e  in
                                         uu____15247.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15246 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15253,uu____15254))
                                           ->
                                           let uu____15263 =
                                             let uu____15264 =
                                               FStar_Syntax_Subst.compress e1
                                                in
                                             uu____15264.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____15263 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15270,msrc,uu____15272))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15281 =
                                                  FStar_Syntax_Subst.compress
                                                    e2
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____15281
                                            | uu____15282 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15283 ->
                                           FStar_Pervasives_Native.None
                                        in
                                     let uu____15284 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     (match uu____15284 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___1929_15289 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___1929_15289.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___1929_15289.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___1929_15289.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e;
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___1929_15289.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___1929_15289.FStar_Syntax_Syntax.lbpos)
                                            }  in
                                          let uu____15290 =
                                            FStar_List.tl stack  in
                                          let uu____15291 =
                                            let uu____15292 =
                                              let uu____15299 =
                                                let uu____15300 =
                                                  let uu____15314 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body
                                                     in
                                                  ((false, [lb1]),
                                                    uu____15314)
                                                   in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15300
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15299
                                               in
                                            uu____15292
                                              FStar_Pervasives_Native.None
                                              top2.FStar_Syntax_Syntax.pos
                                             in
                                          norm cfg env uu____15290
                                            uu____15291
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15330 =
                                            let uu____15332 = is_return body
                                               in
                                            match uu____15332 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15337;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15338;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15341 -> false  in
                                          if uu____15330
                                          then
                                            norm cfg env stack
                                              lb.FStar_Syntax_Syntax.lbdef
                                          else
                                            (let rng =
                                               top2.FStar_Syntax_Syntax.pos
                                                in
                                             let head1 =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 lb.FStar_Syntax_Syntax.lbdef
                                                in
                                             let uu____15356 =
                                               let bv =
                                                 FStar_Syntax_Syntax.new_bv
                                                   FStar_Pervasives_Native.None
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let lb1 =
                                                 let uu____15365 =
                                                   let uu____15368 =
                                                     let uu____15379 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         x.FStar_Syntax_Syntax.sort
                                                        in
                                                     [uu____15379]  in
                                                   FStar_Syntax_Util.mk_app
                                                     repr uu____15368
                                                    in
                                                 let uu____15404 =
                                                   let uu____15405 =
                                                     FStar_TypeChecker_Env.is_total_effect
                                                       cfg.FStar_TypeChecker_Cfg.tcenv
                                                       eff_name
                                                      in
                                                   if uu____15405
                                                   then
                                                     FStar_Parser_Const.effect_Tot_lid
                                                   else
                                                     FStar_Parser_Const.effect_Dv_lid
                                                    in
                                                 {
                                                   FStar_Syntax_Syntax.lbname
                                                     = (FStar_Util.Inl bv);
                                                   FStar_Syntax_Syntax.lbunivs
                                                     = [];
                                                   FStar_Syntax_Syntax.lbtyp
                                                     = uu____15365;
                                                   FStar_Syntax_Syntax.lbeff
                                                     = uu____15404;
                                                   FStar_Syntax_Syntax.lbdef
                                                     = head1;
                                                   FStar_Syntax_Syntax.lbattrs
                                                     = [];
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (head1.FStar_Syntax_Syntax.pos)
                                                 }  in
                                               let uu____15412 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   bv
                                                  in
                                               (lb1, bv, uu____15412)  in
                                             match uu____15356 with
                                             | (lb_head,head_bv,head2) ->
                                                 let body1 =
                                                   FStar_All.pipe_left
                                                     FStar_Syntax_Util.mk_reify
                                                     body
                                                    in
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
                                                   }  in
                                                 let body2 =
                                                   let uu____15429 =
                                                     let uu____15436 =
                                                       let uu____15437 =
                                                         let uu____15456 =
                                                           let uu____15465 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x
                                                              in
                                                           [uu____15465]  in
                                                         (uu____15456, body1,
                                                           (FStar_Pervasives_Native.Some
                                                              body_rc))
                                                          in
                                                       FStar_Syntax_Syntax.Tm_abs
                                                         uu____15437
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15436
                                                      in
                                                   uu____15429
                                                     FStar_Pervasives_Native.None
                                                     body1.FStar_Syntax_Syntax.pos
                                                    in
                                                 let close1 =
                                                   closure_as_term cfg env
                                                    in
                                                 let bind_inst =
                                                   let uu____15504 =
                                                     let uu____15505 =
                                                       FStar_Syntax_Subst.compress
                                                         bind_repr
                                                        in
                                                     uu____15505.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____15504 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (bind1,uu____15511::uu____15512::[])
                                                       ->
                                                       let uu____15517 =
                                                         let uu____15524 =
                                                           let uu____15525 =
                                                             let uu____15532
                                                               =
                                                               let uu____15533
                                                                 =
                                                                 let uu____15534
                                                                   =
                                                                   close1
                                                                    lb.FStar_Syntax_Syntax.lbtyp
                                                                    in
                                                                 (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                                   uu____15534
                                                                  in
                                                               let uu____15535
                                                                 =
                                                                 let uu____15538
                                                                   =
                                                                   let uu____15539
                                                                    =
                                                                    close1 t
                                                                     in
                                                                   (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                    cfg.FStar_TypeChecker_Cfg.tcenv
                                                                    uu____15539
                                                                    in
                                                                 [uu____15538]
                                                                  in
                                                               uu____15533 ::
                                                                 uu____15535
                                                                in
                                                             (bind1,
                                                               uu____15532)
                                                              in
                                                           FStar_Syntax_Syntax.Tm_uinst
                                                             uu____15525
                                                            in
                                                         FStar_Syntax_Syntax.mk
                                                           uu____15524
                                                          in
                                                       uu____15517
                                                         FStar_Pervasives_Native.None
                                                         rng
                                                   | uu____15542 ->
                                                       failwith
                                                         "NIY : Reification of indexed effects"
                                                    in
                                                 let maybe_range_arg =
                                                   let uu____15557 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____15557
                                                   then
                                                     let uu____15570 =
                                                       let uu____15579 =
                                                         FStar_TypeChecker_Cfg.embed_simple
                                                           FStar_Syntax_Embeddings.e_range
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                          in
                                                       FStar_Syntax_Syntax.as_arg
                                                         uu____15579
                                                        in
                                                     let uu____15580 =
                                                       let uu____15591 =
                                                         let uu____15600 =
                                                           FStar_TypeChecker_Cfg.embed_simple
                                                             FStar_Syntax_Embeddings.e_range
                                                             body2.FStar_Syntax_Syntax.pos
                                                             body2.FStar_Syntax_Syntax.pos
                                                            in
                                                         FStar_Syntax_Syntax.as_arg
                                                           uu____15600
                                                          in
                                                       [uu____15591]  in
                                                     uu____15570 ::
                                                       uu____15580
                                                   else []  in
                                                 let reified =
                                                   let args =
                                                     let uu____15649 =
                                                       FStar_Syntax_Util.is_layered
                                                         ed
                                                        in
                                                     if uu____15649
                                                     then
                                                       let unit_args =
                                                         let uu____15673 =
                                                           let uu____15674 =
                                                             let uu____15677
                                                               =
                                                               let uu____15678
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15678
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15677
                                                               FStar_Syntax_Subst.compress
                                                              in
                                                           uu____15674.FStar_Syntax_Syntax.n
                                                            in
                                                         match uu____15673
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_arrow
                                                             (uu____15719::uu____15720::bs,uu____15722)
                                                             when
                                                             (FStar_List.length
                                                                bs)
                                                               >=
                                                               (Prims.of_int (2))
                                                             ->
                                                             let uu____15774
                                                               =
                                                               let uu____15783
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   bs
                                                                   (FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2))))
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15783
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15774
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____15914
                                                                     ->
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.unit_const))
                                                         | uu____15921 ->
                                                             let uu____15922
                                                               =
                                                               let uu____15928
                                                                 =
                                                                 let uu____15930
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    ed.FStar_Syntax_Syntax.mname
                                                                    in
                                                                 let uu____15932
                                                                   =
                                                                   let uu____15934
                                                                    =
                                                                    let uu____15935
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    ed
                                                                    FStar_Syntax_Util.get_bind_vc_combinator
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15935
                                                                    FStar_Pervasives_Native.snd
                                                                     in
                                                                   FStar_All.pipe_right
                                                                    uu____15934
                                                                    FStar_Syntax_Print.term_to_string
                                                                    in
                                                                 FStar_Util.format2
                                                                   "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                                   uu____15930
                                                                   uu____15932
                                                                  in
                                                               (FStar_Errors.Fatal_UnexpectedEffect,
                                                                 uu____15928)
                                                                in
                                                             FStar_Errors.raise_error
                                                               uu____15922
                                                               rng
                                                          in
                                                       let uu____15969 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let uu____15978 =
                                                         let uu____15989 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t
                                                            in
                                                         let uu____15998 =
                                                           let uu____16009 =
                                                             let uu____16020
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2
                                                                in
                                                             let uu____16029
                                                               =
                                                               let uu____16040
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   body2
                                                                  in
                                                               [uu____16040]
                                                                in
                                                             uu____16020 ::
                                                               uu____16029
                                                              in
                                                           FStar_List.append
                                                             unit_args
                                                             uu____16009
                                                            in
                                                         uu____15989 ::
                                                           uu____15998
                                                          in
                                                       uu____15969 ::
                                                         uu____15978
                                                     else
                                                       (let uu____16099 =
                                                          let uu____16110 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              lb.FStar_Syntax_Syntax.lbtyp
                                                             in
                                                          let uu____16119 =
                                                            let uu____16130 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t
                                                               in
                                                            [uu____16130]  in
                                                          uu____16110 ::
                                                            uu____16119
                                                           in
                                                        let uu____16163 =
                                                          let uu____16174 =
                                                            let uu____16185 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            let uu____16194 =
                                                              let uu____16205
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  head2
                                                                 in
                                                              let uu____16214
                                                                =
                                                                let uu____16225
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.tun
                                                                   in
                                                                let uu____16234
                                                                  =
                                                                  let uu____16245
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    body2  in
                                                                  [uu____16245]
                                                                   in
                                                                uu____16225
                                                                  ::
                                                                  uu____16234
                                                                 in
                                                              uu____16205 ::
                                                                uu____16214
                                                               in
                                                            uu____16185 ::
                                                              uu____16194
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____16174
                                                           in
                                                        FStar_List.append
                                                          uu____16099
                                                          uu____16163)
                                                      in
                                                   let uu____16310 =
                                                     let uu____16317 =
                                                       let uu____16318 =
                                                         let uu____16332 =
                                                           let uu____16335 =
                                                             let uu____16342
                                                               =
                                                               let uu____16343
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   head_bv
                                                                  in
                                                               [uu____16343]
                                                                in
                                                             FStar_Syntax_Subst.close
                                                               uu____16342
                                                              in
                                                           let uu____16362 =
                                                             FStar_Syntax_Syntax.mk
                                                               (FStar_Syntax_Syntax.Tm_app
                                                                  (bind_inst,
                                                                    args))
                                                               FStar_Pervasives_Native.None
                                                               rng
                                                              in
                                                           FStar_All.pipe_left
                                                             uu____16335
                                                             uu____16362
                                                            in
                                                         ((false, [lb_head]),
                                                           uu____16332)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_let
                                                         uu____16318
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____16317
                                                      in
                                                   uu____16310
                                                     FStar_Pervasives_Native.None
                                                     rng
                                                    in
                                                 (FStar_TypeChecker_Cfg.log
                                                    cfg
                                                    (fun uu____16394  ->
                                                       let uu____16395 =
                                                         FStar_Syntax_Print.term_to_string
                                                           top0
                                                          in
                                                       let uu____16397 =
                                                         FStar_Syntax_Print.term_to_string
                                                           reified
                                                          in
                                                       FStar_Util.print2
                                                         "Reified (1) <%s> to %s\n"
                                                         uu____16395
                                                         uu____16397);
                                                  (let uu____16400 =
                                                     FStar_List.tl stack  in
                                                   norm cfg env uu____16400
                                                     reified)))))))
                  | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                      ((let uu____16428 = FStar_Options.defensive ()  in
                        if uu____16428
                        then
                          let is_arg_impure uu____16443 =
                            match uu____16443 with
                            | (e,q) ->
                                let uu____16457 =
                                  let uu____16458 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16458.FStar_Syntax_Syntax.n  in
                                (match uu____16457 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____16474 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____16474
                                 | uu____16476 -> false)
                             in
                          let uu____16478 =
                            let uu____16480 =
                              let uu____16491 =
                                FStar_Syntax_Syntax.as_arg head1  in
                              uu____16491 :: args  in
                            FStar_Util.for_some is_arg_impure uu____16480  in
                          (if uu____16478
                           then
                             let uu____16517 =
                               let uu____16523 =
                                 let uu____16525 =
                                   FStar_Syntax_Print.term_to_string top2  in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____16525
                                  in
                               (FStar_Errors.Warning_Defensive, uu____16523)
                                in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu____16517
                           else ())
                        else ());
                       (let fallback1 uu____16538 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16542  ->
                               let uu____16543 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____16543 "");
                          (let uu____16547 = FStar_List.tl stack  in
                           let uu____16548 = FStar_Syntax_Util.mk_reify top2
                              in
                           norm cfg env uu____16547 uu____16548)
                           in
                        let fallback2 uu____16554 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16558  ->
                               let uu____16559 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____16559 "");
                          (let uu____16563 = FStar_List.tl stack  in
                           let uu____16564 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____16563 uu____16564)
                           in
                        let uu____16569 =
                          let uu____16570 = FStar_Syntax_Util.un_uinst head1
                             in
                          uu____16570.FStar_Syntax_Syntax.n  in
                        match uu____16569 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____16576 =
                              let uu____16578 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____16578  in
                            if uu____16576
                            then fallback1 ()
                            else
                              (let uu____16583 =
                                 let uu____16585 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____16585  in
                               if uu____16583
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____16602 =
                                      let uu____16607 =
                                        FStar_Syntax_Util.mk_reify head1  in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____16607 args
                                       in
                                    uu____16602 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____16608 = FStar_List.tl stack  in
                                  norm cfg env uu____16608 t1))
                        | uu____16609 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____16611) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____16635 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____16635  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____16639  ->
                            let uu____16640 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____16640);
                       (let uu____16643 = FStar_List.tl stack  in
                        norm cfg env uu____16643 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____16764  ->
                                match uu____16764 with
                                | (pat,wopt,tm) ->
                                    let uu____16812 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16812)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          top2.FStar_Syntax_Syntax.pos
                         in
                      let uu____16844 = FStar_List.tl stack  in
                      norm cfg env uu____16844 tm
                  | uu____16845 -> fallback ()))

and (reify_lift :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.monad_name ->
        FStar_Syntax_Syntax.monad_name ->
          FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun e  ->
      fun msrc  ->
        fun mtgt  ->
          fun t  ->
            let env = cfg.FStar_TypeChecker_Cfg.tcenv  in
            FStar_TypeChecker_Cfg.log cfg
              (fun uu____16859  ->
                 let uu____16860 = FStar_Ident.string_of_lid msrc  in
                 let uu____16862 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16864 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16860
                   uu____16862 uu____16864);
            (let uu____16867 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16870 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env)
                     in
                  Prims.op_Negation uu____16870)
                in
             if uu____16867
             then
               let ed =
                 let uu____16875 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16875  in
               let uu____16876 =
                 let uu____16885 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 FStar_All.pipe_right uu____16885 FStar_Util.must  in
               match uu____16876 with
               | (uu____16932,repr) ->
                   let uu____16942 =
                     let uu____16951 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr
                        in
                     FStar_All.pipe_right uu____16951 FStar_Util.must  in
                   (match uu____16942 with
                    | (uu____16998,return_repr) ->
                        let return_inst =
                          let uu____17011 =
                            let uu____17012 =
                              FStar_Syntax_Subst.compress return_repr  in
                            uu____17012.FStar_Syntax_Syntax.n  in
                          match uu____17011 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm,uu____17018::[]) ->
                              let uu____17023 =
                                let uu____17030 =
                                  let uu____17031 =
                                    let uu____17038 =
                                      let uu____17039 =
                                        env.FStar_TypeChecker_Env.universe_of
                                          env t
                                         in
                                      [uu____17039]  in
                                    (return_tm, uu____17038)  in
                                  FStar_Syntax_Syntax.Tm_uinst uu____17031
                                   in
                                FStar_Syntax_Syntax.mk uu____17030  in
                              uu____17023 FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                          | uu____17042 ->
                              failwith "NIY : Reification of indexed effects"
                           in
                        let uu____17046 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t
                             in
                          let lb =
                            let uu____17057 =
                              let uu____17060 =
                                let uu____17071 =
                                  FStar_Syntax_Syntax.as_arg t  in
                                [uu____17071]  in
                              FStar_Syntax_Util.mk_app repr uu____17060  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Util.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu____17057;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            }  in
                          let uu____17098 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (lb, bv, uu____17098)  in
                        (match uu____17046 with
                         | (lb_e,e_bv,e1) ->
                             let uu____17110 =
                               let uu____17117 =
                                 let uu____17118 =
                                   let uu____17132 =
                                     let uu____17135 =
                                       let uu____17142 =
                                         let uu____17143 =
                                           FStar_Syntax_Syntax.mk_binder e_bv
                                            in
                                         [uu____17143]  in
                                       FStar_Syntax_Subst.close uu____17142
                                        in
                                     let uu____17162 =
                                       let uu____17163 =
                                         let uu____17170 =
                                           let uu____17171 =
                                             let uu____17188 =
                                               let uu____17199 =
                                                 FStar_Syntax_Syntax.as_arg t
                                                  in
                                               let uu____17208 =
                                                 let uu____17219 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     e1
                                                    in
                                                 [uu____17219]  in
                                               uu____17199 :: uu____17208  in
                                             (return_inst, uu____17188)  in
                                           FStar_Syntax_Syntax.Tm_app
                                             uu____17171
                                            in
                                         FStar_Syntax_Syntax.mk uu____17170
                                          in
                                       uu____17163
                                         FStar_Pervasives_Native.None
                                         e1.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_All.pipe_left uu____17135
                                       uu____17162
                                      in
                                   ((false, [lb_e]), uu____17132)  in
                                 FStar_Syntax_Syntax.Tm_let uu____17118  in
                               FStar_Syntax_Syntax.mk uu____17117  in
                             uu____17110 FStar_Pervasives_Native.None
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu____17281 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17281 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17284 =
                      let uu____17286 = FStar_Ident.text_of_lid msrc  in
                      let uu____17288 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17286 uu____17288
                       in
                    failwith uu____17284
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17291;
                      FStar_TypeChecker_Env.mtarget = uu____17292;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17293;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17313 =
                      let uu____17315 = FStar_Ident.text_of_lid msrc  in
                      let uu____17317 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17315 uu____17317
                       in
                    failwith uu____17313
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17320;
                      FStar_TypeChecker_Env.mtarget = uu____17321;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17322;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____17353 =
                        FStar_TypeChecker_Env.is_reifiable_effect env msrc
                         in
                      if uu____17353
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____17358 =
                           let uu____17365 =
                             let uu____17366 =
                               let uu____17385 =
                                 let uu____17394 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____17394]  in
                               (uu____17385, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____17366  in
                           FStar_Syntax_Syntax.mk uu____17365  in
                         uu____17358 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____17427 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    lift uu____17427 t e1))

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
  fun cfg  ->
    fun env  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____17497  ->
                   match uu____17497 with
                   | (a,imp) ->
                       let uu____17516 = norm cfg env [] a  in
                       (uu____17516, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17526  ->
             let uu____17527 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17529 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17527 uu____17529);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17555 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17558  -> FStar_Pervasives_Native.Some _17558)
                     uu____17555
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2110_17559 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2110_17559.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2110_17559.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17581 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17584  -> FStar_Pervasives_Native.Some _17584)
                     uu____17581
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2121_17585 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2121_17585.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2121_17585.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17630  ->
                      match uu____17630 with
                      | (a,i) ->
                          let uu____17650 = norm cfg env [] a  in
                          (uu____17650, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17672  ->
                       match uu___14_17672 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17676 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17676
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2138_17684 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2140_17687 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2140_17687.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2138_17684.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2138_17684.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____17691 = b  in
        match uu____17691 with
        | (x,imp) ->
            let x1 =
              let uu___2148_17699 = x  in
              let uu____17700 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2148_17699.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2148_17699.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17700
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____17711 =
                    let uu____17712 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____17712  in
                  FStar_Pervasives_Native.Some uu____17711
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17723 =
          FStar_List.fold_left
            (fun uu____17757  ->
               fun b  ->
                 match uu____17757 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17723 with | (nbs,uu____17837) -> FStar_List.rev nbs

and (norm_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____17869 =
              let uu___2173_17870 = rc  in
              let uu____17871 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2173_17870.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17871;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2173_17870.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17869
        | uu____17889 -> lopt

and (maybe_simplify :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env stack tm  in
          if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.b380
          then
            (let uu____17899 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17901 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17899 uu____17901)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_17913  ->
      match uu___15_17913 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17926 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17926 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17930 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____17930)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____17938 = norm_cb cfg  in
            reduce_primops uu____17938 cfg env tm  in
          let uu____17943 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17943
          then tm1
          else
            (let w t =
               let uu___2202_17962 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2202_17962.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2202_17962.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17974 =
                 let uu____17975 = FStar_Syntax_Util.unmeta t  in
                 uu____17975.FStar_Syntax_Syntax.n  in
               match uu____17974 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17987 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18051)::args1,(bv,uu____18054)::bs1) ->
                   let uu____18108 =
                     let uu____18109 = FStar_Syntax_Subst.compress t  in
                     uu____18109.FStar_Syntax_Syntax.n  in
                   (match uu____18108 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18114 -> false)
               | ([],[]) -> true
               | (uu____18145,uu____18146) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18197 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18199 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18197
                    uu____18199)
               else ();
               (let uu____18204 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18204 with
                | (hd1,args) ->
                    let uu____18243 =
                      let uu____18244 = FStar_Syntax_Subst.compress hd1  in
                      uu____18244.FStar_Syntax_Syntax.n  in
                    (match uu____18243 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____18252 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18254 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18256 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18252 uu____18254 uu____18256)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18261 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18279 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18281 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18279
                    uu____18281)
               else ();
               (let uu____18286 = FStar_Syntax_Util.is_squash t  in
                match uu____18286 with
                | FStar_Pervasives_Native.Some (uu____18297,t') ->
                    is_applied bs t'
                | uu____18309 ->
                    let uu____18318 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18318 with
                     | FStar_Pervasives_Native.Some (uu____18329,t') ->
                         is_applied bs t'
                     | uu____18341 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18365 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18365 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18372)::(q,uu____18374)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18417 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18419 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18417 uu____18419)
                    else ();
                    (let uu____18424 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18424 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18429 =
                           let uu____18430 = FStar_Syntax_Subst.compress p
                              in
                           uu____18430.FStar_Syntax_Syntax.n  in
                         (match uu____18429 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18441 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18441))
                          | uu____18444 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18447)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18472 =
                           let uu____18473 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18473.FStar_Syntax_Syntax.n  in
                         (match uu____18472 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18484 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18484))
                          | uu____18487 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18491 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18491 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18496 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18496 with
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
                                               FStar_Syntax_Util.ktype0))
                                        in
                                     let uu____18510 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18510))
                               | uu____18513 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18518)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18543 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18543 with
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
                                               FStar_Syntax_Util.ktype0))
                                        in
                                     let uu____18557 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18557))
                               | uu____18560 -> FStar_Pervasives_Native.None)
                          | uu____18563 -> FStar_Pervasives_Native.None)
                     | uu____18566 -> FStar_Pervasives_Native.None))
               | uu____18569 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18582 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18582 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18588)::[],uu____18589,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18609 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18611 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18609
                         uu____18611)
                    else ();
                    is_quantified_const bv phi')
               | uu____18616 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18631 =
                 let uu____18632 = FStar_Syntax_Subst.compress phi  in
                 uu____18632.FStar_Syntax_Syntax.n  in
               match uu____18631 with
               | FStar_Syntax_Syntax.Tm_match (uu____18638,br::brs) ->
                   let uu____18705 = br  in
                   (match uu____18705 with
                    | (uu____18723,uu____18724,e) ->
                        let r =
                          let uu____18746 = simp_t e  in
                          match uu____18746 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18758 =
                                FStar_List.for_all
                                  (fun uu____18777  ->
                                     match uu____18777 with
                                     | (uu____18791,uu____18792,e') ->
                                         let uu____18806 = simp_t e'  in
                                         uu____18806 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18758
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18822 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18832 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18832
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18870 =
                 match uu____18870 with
                 | (t1,q) ->
                     let uu____18891 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18891 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18923 -> (t1, q))
                  in
               let uu____18936 = FStar_Syntax_Util.head_and_args t  in
               match uu____18936 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____19016 =
                 let uu____19017 = FStar_Syntax_Util.unmeta ty  in
                 uu____19017.FStar_Syntax_Syntax.n  in
               match uu____19016 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____19022) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____19027,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____19051 -> false  in
             let simplify1 arg =
               let uu____19084 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____19084, arg)  in
             let uu____19099 = is_forall_const tm1  in
             match uu____19099 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____19105 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____19107 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____19105
                       uu____19107)
                  else ();
                  (let uu____19112 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____19112))
             | FStar_Pervasives_Native.None  ->
                 let uu____19113 =
                   let uu____19114 = FStar_Syntax_Subst.compress tm1  in
                   uu____19114.FStar_Syntax_Syntax.n  in
                 (match uu____19113 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19118;
                              FStar_Syntax_Syntax.vars = uu____19119;_},uu____19120);
                         FStar_Syntax_Syntax.pos = uu____19121;
                         FStar_Syntax_Syntax.vars = uu____19122;_},args)
                      ->
                      let uu____19152 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19152
                      then
                        let uu____19155 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19155 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19213)::
                             (uu____19214,(arg,uu____19216))::[] ->
                             maybe_auto_squash arg
                         | (uu____19289,(arg,uu____19291))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19292)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19365)::uu____19366::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19436::(FStar_Pervasives_Native.Some (false
                                         ),uu____19437)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19507 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19525 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19525
                         then
                           let uu____19528 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19528 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19586)::uu____19587::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19657::(FStar_Pervasives_Native.Some (true
                                           ),uu____19658)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19728)::(uu____19729,(arg,uu____19731))::[]
                               -> maybe_auto_squash arg
                           | (uu____19804,(arg,uu____19806))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19807)::[]
                               -> maybe_auto_squash arg
                           | uu____19880 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19898 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19898
                            then
                              let uu____19901 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19901 with
                              | uu____19959::(FStar_Pervasives_Native.Some
                                              (true ),uu____19960)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20030)::uu____20031::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20101)::(uu____20102,(arg,uu____20104))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20177,(p,uu____20179))::(uu____20180,
                                                                (q,uu____20182))::[]
                                  ->
                                  let uu____20254 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20254
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20259 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20277 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20277
                               then
                                 let uu____20280 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20280 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20338)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20339)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20413)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20414)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20488)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20489)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20563)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20564)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20638,(arg,uu____20640))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20641)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20714)::(uu____20715,(arg,uu____20717))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20790,(arg,uu____20792))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20793)::[]
                                     ->
                                     let uu____20866 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20866
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20867)::(uu____20868,(arg,uu____20870))::[]
                                     ->
                                     let uu____20943 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20943
                                 | (uu____20944,(p,uu____20946))::(uu____20947,
                                                                   (q,uu____20949))::[]
                                     ->
                                     let uu____21021 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21021
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21026 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21044 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21044
                                  then
                                    let uu____21047 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21047 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21105)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21149)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21193 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21211 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21211
                                     then
                                       match args with
                                       | (t,uu____21215)::[] ->
                                           let uu____21240 =
                                             let uu____21241 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21241.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21240 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21244::[],body,uu____21246)
                                                ->
                                                let uu____21281 = simp_t body
                                                   in
                                                (match uu____21281 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21287 -> tm1)
                                            | uu____21291 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21293))::(t,uu____21295)::[]
                                           ->
                                           let uu____21335 =
                                             let uu____21336 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21336.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21335 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21339::[],body,uu____21341)
                                                ->
                                                let uu____21376 = simp_t body
                                                   in
                                                (match uu____21376 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21384 -> tm1)
                                            | uu____21388 -> tm1)
                                       | uu____21389 -> tm1
                                     else
                                       (let uu____21402 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21402
                                        then
                                          match args with
                                          | (t,uu____21406)::[] ->
                                              let uu____21431 =
                                                let uu____21432 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21432.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21431 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21435::[],body,uu____21437)
                                                   ->
                                                   let uu____21472 =
                                                     simp_t body  in
                                                   (match uu____21472 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21478 -> tm1)
                                               | uu____21482 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21484))::(t,uu____21486)::[]
                                              ->
                                              let uu____21526 =
                                                let uu____21527 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21527.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21526 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21530::[],body,uu____21532)
                                                   ->
                                                   let uu____21567 =
                                                     simp_t body  in
                                                   (match uu____21567 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____21575 -> tm1)
                                               | uu____21579 -> tm1)
                                          | uu____21580 -> tm1
                                        else
                                          (let uu____21593 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21593
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21596;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21597;_},uu____21598)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21624;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21625;_},uu____21626)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21652 -> tm1
                                           else
                                             (let uu____21665 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____21665
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____21679 =
                                                    let uu____21680 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____21680.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____21679 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21691 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21705 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____21705
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____21744 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____21744
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21750 =
                                                         let uu____21751 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____21751.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____21750 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21754 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____21762 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____21762
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21771
                                                                  =
                                                                  let uu____21772
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____21772.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____21771
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____21778)
                                                                    -> hd1
                                                                | uu____21803
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____21807
                                                                =
                                                                let uu____21818
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____21818]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21807)
                                                       | uu____21851 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21856 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____21856 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21876 ->
                                                     let uu____21885 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____21885 cfg env
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21891;
                         FStar_Syntax_Syntax.vars = uu____21892;_},args)
                      ->
                      let uu____21918 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21918
                      then
                        let uu____21921 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21921 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21979)::
                             (uu____21980,(arg,uu____21982))::[] ->
                             maybe_auto_squash arg
                         | (uu____22055,(arg,uu____22057))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22058)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22131)::uu____22132::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22202::(FStar_Pervasives_Native.Some (false
                                         ),uu____22203)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22273 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22291 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22291
                         then
                           let uu____22294 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22294 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22352)::uu____22353::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22423::(FStar_Pervasives_Native.Some (true
                                           ),uu____22424)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22494)::(uu____22495,(arg,uu____22497))::[]
                               -> maybe_auto_squash arg
                           | (uu____22570,(arg,uu____22572))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22573)::[]
                               -> maybe_auto_squash arg
                           | uu____22646 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22664 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22664
                            then
                              let uu____22667 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____22667 with
                              | uu____22725::(FStar_Pervasives_Native.Some
                                              (true ),uu____22726)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22796)::uu____22797::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22867)::(uu____22868,(arg,uu____22870))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22943,(p,uu____22945))::(uu____22946,
                                                                (q,uu____22948))::[]
                                  ->
                                  let uu____23020 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23020
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23025 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23043 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23043
                               then
                                 let uu____23046 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23046 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23104)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23105)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23179)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23180)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23254)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23255)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23329)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23330)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23404,(arg,uu____23406))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23407)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23480)::(uu____23481,(arg,uu____23483))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23556,(arg,uu____23558))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23559)::[]
                                     ->
                                     let uu____23632 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23632
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23633)::(uu____23634,(arg,uu____23636))::[]
                                     ->
                                     let uu____23709 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23709
                                 | (uu____23710,(p,uu____23712))::(uu____23713,
                                                                   (q,uu____23715))::[]
                                     ->
                                     let uu____23787 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23787
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23792 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23810 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23810
                                  then
                                    let uu____23813 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23813 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23871)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23915)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23959 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23977 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23977
                                     then
                                       match args with
                                       | (t,uu____23981)::[] ->
                                           let uu____24006 =
                                             let uu____24007 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24007.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24006 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24010::[],body,uu____24012)
                                                ->
                                                let uu____24047 = simp_t body
                                                   in
                                                (match uu____24047 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24053 -> tm1)
                                            | uu____24057 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24059))::(t,uu____24061)::[]
                                           ->
                                           let uu____24101 =
                                             let uu____24102 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24102.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24101 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24105::[],body,uu____24107)
                                                ->
                                                let uu____24142 = simp_t body
                                                   in
                                                (match uu____24142 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24150 -> tm1)
                                            | uu____24154 -> tm1)
                                       | uu____24155 -> tm1
                                     else
                                       (let uu____24168 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24168
                                        then
                                          match args with
                                          | (t,uu____24172)::[] ->
                                              let uu____24197 =
                                                let uu____24198 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24198.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24197 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24201::[],body,uu____24203)
                                                   ->
                                                   let uu____24238 =
                                                     simp_t body  in
                                                   (match uu____24238 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24244 -> tm1)
                                               | uu____24248 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24250))::(t,uu____24252)::[]
                                              ->
                                              let uu____24292 =
                                                let uu____24293 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24293.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24292 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24296::[],body,uu____24298)
                                                   ->
                                                   let uu____24333 =
                                                     simp_t body  in
                                                   (match uu____24333 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | FStar_Pervasives_Native.Some
                                                        (true ) when
                                                        clearly_inhabited ty
                                                        ->
                                                        w
                                                          FStar_Syntax_Util.t_true
                                                    | uu____24341 -> tm1)
                                               | uu____24345 -> tm1)
                                          | uu____24346 -> tm1
                                        else
                                          (let uu____24359 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24359
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24362;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24363;_},uu____24364)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24390;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24391;_},uu____24392)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24418 -> tm1
                                           else
                                             (let uu____24431 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____24431
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____24445 =
                                                    let uu____24446 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____24446.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____24445 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____24457 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24471 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____24471
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____24506 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____24506
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24512 =
                                                         let uu____24513 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____24513.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____24512 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24516 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24524 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24524
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24533
                                                                  =
                                                                  let uu____24534
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24534.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24533
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____24540)
                                                                    -> hd1
                                                                | uu____24565
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____24569
                                                                =
                                                                let uu____24580
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____24580]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24569)
                                                       | uu____24613 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24618 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____24618 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24638 ->
                                                     let uu____24647 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____24647 cfg env
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24658 = simp_t t  in
                      (match uu____24658 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24667 ->
                      let uu____24690 = is_const_match tm1  in
                      (match uu____24690 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24699 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____24709  ->
               (let uu____24711 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24713 = FStar_Syntax_Print.term_to_string t  in
                let uu____24715 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24723 =
                  let uu____24725 =
                    let uu____24728 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24728
                     in
                  stack_to_string uu____24725  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24711 uu____24713 uu____24715 uu____24723);
               (let uu____24753 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24753
                then
                  let uu____24757 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24757 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24764 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24766 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24768 =
                          let uu____24770 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24770
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24764
                          uu____24766 uu____24768);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____24792 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____24800)::uu____24801 -> true
                | uu____24811 -> false)
              in
           if uu____24792
           then
             let uu____24814 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____24814 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____24828 =
                        let uu____24830 =
                          let uu____24832 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____24832  in
                        FStar_Util.string_of_int uu____24830  in
                      let uu____24839 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____24841 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                      let uu____24843 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____24828 uu____24839 uu____24841 uu____24843)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____24852,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24881  ->
                        let uu____24882 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24882);
                   rebuild cfg env stack1 t1)
              | (Let (env',bs,lb,r))::stack1 ->
                  let body = FStar_Syntax_Subst.close bs t1  in
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env' stack1 t2
              | (Abs (env',bs,env'',lopt,r))::stack1 ->
                  let bs1 = norm_binders cfg env' bs  in
                  let lopt1 = norm_lcomp_opt cfg env'' lopt  in
                  let uu____24925 =
                    let uu___2831_24926 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2831_24926.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2831_24926.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____24925
              | (Arg (Univ uu____24929,uu____24930,uu____24931))::uu____24932
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____24936,uu____24937))::uu____24938 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____24954,uu____24955),aq,r))::stack1
                  when
                  let uu____25007 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____25007 ->
                  let t2 =
                    let uu____25011 =
                      let uu____25016 =
                        let uu____25017 = closure_as_term cfg env_arg tm  in
                        (uu____25017, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____25016  in
                    uu____25011 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____25027),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____25082  ->
                        let uu____25083 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____25083);
                   if
                     Prims.op_Negation
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                   then
                     (if
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                      then
                        let arg = closure_as_term cfg env_arg tm  in
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                            FStar_Pervasives_Native.None r
                           in
                        rebuild cfg env_arg stack1 t2
                      else
                        (let stack2 = (App (env, t1, aq, r)) :: stack1  in
                         norm cfg env_arg stack2 tm))
                   else
                     (let uu____25103 = FStar_ST.op_Bang m  in
                      match uu____25103 with
                      | FStar_Pervasives_Native.None  ->
                          if
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          then
                            let arg = closure_as_term cfg env_arg tm  in
                            let t2 =
                              FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                                FStar_Pervasives_Native.None r
                               in
                            rebuild cfg env_arg stack1 t2
                          else
                            (let stack2 = (MemoLazy m) ::
                               (App (env, t1, aq, r)) :: stack1  in
                             norm cfg env_arg stack2 tm)
                      | FStar_Pervasives_Native.Some (uu____25191,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____25247 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____25252  ->
                         let uu____25253 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____25253);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____25263 =
                    let uu____25264 = FStar_Syntax_Subst.compress t1  in
                    uu____25264.FStar_Syntax_Syntax.n  in
                  (match uu____25263 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____25292 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____25292  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____25296  ->
                             let uu____25297 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____25297);
                        (let uu____25300 = FStar_List.tl stack  in
                         norm cfg env1 uu____25300 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____25301);
                          FStar_Syntax_Syntax.pos = uu____25302;
                          FStar_Syntax_Syntax.vars = uu____25303;_},(e,uu____25305)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____25344 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____25361 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____25361 with
                        | (hd1,args) ->
                            let uu____25404 =
                              let uu____25405 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____25405.FStar_Syntax_Syntax.n  in
                            (match uu____25404 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____25409 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____25409 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____25412;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____25413;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____25414;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____25416;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____25417;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____25418;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____25419;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____25455 -> fallback " (3)" ())
                             | uu____25459 -> fallback " (4)" ()))
                   | uu____25461 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (CBVApp (env',head1,aq,r))::stack1 ->
                  let uu____25484 =
                    let uu____25485 =
                      let uu____25486 =
                        let uu____25493 =
                          let uu____25494 =
                            let uu____25526 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env, t1, uu____25526, false)  in
                          Clos uu____25494  in
                        (uu____25493, aq, (t1.FStar_Syntax_Syntax.pos))  in
                      Arg uu____25486  in
                    uu____25485 :: stack1  in
                  norm cfg env' uu____25484 head1
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____25601  ->
                        let uu____25602 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____25602);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____25613 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25618  ->
                           let uu____25619 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____25621 =
                             let uu____25623 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____25653  ->
                                       match uu____25653 with
                                       | (p,uu____25664,uu____25665) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____25623
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____25619 uu____25621);
                      (let whnf =
                         (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                           ||
                           (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          in
                       let cfg_exclude_zeta =
                         if
                           (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full
                         then cfg1
                         else
                           (let new_delta =
                              FStar_All.pipe_right
                                cfg1.FStar_TypeChecker_Cfg.delta_level
                                (FStar_List.filter
                                   (fun uu___16_25690  ->
                                      match uu___16_25690 with
                                      | FStar_TypeChecker_Env.InliningDelta 
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                           -> true
                                      | uu____25694 -> false))
                               in
                            let steps =
                              let uu___3008_25697 =
                                cfg1.FStar_TypeChecker_Cfg.steps  in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3008_25697.FStar_TypeChecker_Cfg.for_extraction)
                              }  in
                            let uu___3011_25704 = cfg1  in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3011_25704.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3011_25704.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3011_25704.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3011_25704.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3011_25704.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3011_25704.FStar_TypeChecker_Cfg.reifying)
                            })
                          in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____25779 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____25810 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25899  ->
                                       fun uu____25900  ->
                                         match (uu____25899, uu____25900)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____26050 =
                                               norm_pat env3 p1  in
                                             (match uu____26050 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____25810 with
                              | (pats1,env3) ->
                                  ((let uu___3039_26220 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3039_26220.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3043_26241 = x  in
                               let uu____26242 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3043_26241.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3043_26241.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26242
                               }  in
                             ((let uu___3046_26256 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3046_26256.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3050_26267 = x  in
                               let uu____26268 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3050_26267.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3050_26267.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26268
                               }  in
                             ((let uu___3053_26282 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3053_26282.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3059_26298 = x  in
                               let uu____26299 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3059_26298.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3059_26298.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26299
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3063_26314 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3063_26314.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____26358 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____26388 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____26388 with
                                     | (p,wopt,e) ->
                                         let uu____26408 = norm_pat env1 p
                                            in
                                         (match uu____26408 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____26463 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____26463
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____26480 =
                           ((((cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                                &&
                                (Prims.op_Negation
                                   (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak))
                               &&
                               (Prims.op_Negation
                                  (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars))
                              &&
                              (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weakly_reduce_scrutinee)
                             && (maybe_weakly_reduced scrutinee)
                            in
                         if uu____26480
                         then
                           norm
                             (let uu___3082_26487 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3084_26490 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.zeta_full =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.zeta_full);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3084_26490.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3082_26487.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3082_26487.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3082_26487.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3082_26487.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3082_26487.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3082_26487.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3082_26487.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3082_26487.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____26494 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____26494)
                       in
                    let rec is_cons head1 =
                      let uu____26520 =
                        let uu____26521 = FStar_Syntax_Subst.compress head1
                           in
                        uu____26521.FStar_Syntax_Syntax.n  in
                      match uu____26520 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____26526) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____26531 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26533;
                            FStar_Syntax_Syntax.fv_delta = uu____26534;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26536;
                            FStar_Syntax_Syntax.fv_delta = uu____26537;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____26538);_}
                          -> true
                      | uu____26546 -> false  in
                    let guard_when_clause wopt b rest =
                      match wopt with
                      | FStar_Pervasives_Native.None  -> b
                      | FStar_Pervasives_Native.Some w ->
                          let then_branch = b  in
                          let else_branch =
                            mk
                              (FStar_Syntax_Syntax.Tm_match (scrutinee, rest))
                              r
                             in
                          FStar_Syntax_Util.if_then_else w then_branch
                            else_branch
                       in
                    let rec matches_pat scrutinee_orig p =
                      let scrutinee1 =
                        FStar_Syntax_Util.unmeta scrutinee_orig  in
                      let scrutinee2 = FStar_Syntax_Util.unlazy scrutinee1
                         in
                      let uu____26715 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____26715 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____26812 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26854 ->
                                    let uu____26855 =
                                      let uu____26857 = is_cons head1  in
                                      Prims.op_Negation uu____26857  in
                                    FStar_Util.Inr uu____26855)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____26886 =
                                 let uu____26887 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____26887.FStar_Syntax_Syntax.n  in
                               (match uu____26886 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26906 ->
                                    let uu____26907 =
                                      let uu____26909 = is_cons head1  in
                                      Prims.op_Negation uu____26909  in
                                    FStar_Util.Inr uu____26907))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____27000)::rest_a,(p1,uu____27003)::rest_p)
                          ->
                          let uu____27062 = matches_pat t2 p1  in
                          (match uu____27062 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____27115 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____27238 = matches_pat scrutinee1 p1  in
                          (match uu____27238 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____27284  ->
                                     let uu____27285 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____27287 =
                                       let uu____27289 =
                                         FStar_List.map
                                           (fun uu____27301  ->
                                              match uu____27301 with
                                              | (uu____27307,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____27289
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____27285 uu____27287);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____27343  ->
                                          match uu____27343 with
                                          | (bv,t2) ->
                                              let uu____27366 =
                                                let uu____27373 =
                                                  let uu____27376 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____27376
                                                   in
                                                let uu____27377 =
                                                  let uu____27378 =
                                                    let uu____27410 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____27410,
                                                      false)
                                                     in
                                                  Clos uu____27378  in
                                                (uu____27373, uu____27377)
                                                 in
                                              uu____27366 :: env2) env1 s
                                    in
                                 let uu____27503 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____27503)))
                       in
                    if
                      (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    then matches scrutinee branches
                    else norm_and_rebuild_match ()))))

let (normalize_with_primitive_steps :
  FStar_TypeChecker_Cfg.primitive_step Prims.list ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = FStar_TypeChecker_Cfg.config' ps s e  in
          FStar_TypeChecker_Cfg.log_cfg c
            (fun uu____27536  ->
               let uu____27537 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____27537);
          (let uu____27540 = is_nbe_request s  in
           if uu____27540
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27546  ->
                   let uu____27547 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27547);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27553  ->
                   let uu____27554 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27554);
              (let uu____27557 =
                 FStar_Util.record_time (fun uu____27564  -> nbe_eval c s t)
                  in
               match uu____27557 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27573  ->
                         let uu____27574 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27576 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27574 uu____27576);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27584  ->
                   let uu____27585 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27585);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27591  ->
                   let uu____27592 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27592);
              (let uu____27595 =
                 FStar_Util.record_time (fun uu____27602  -> norm c [] [] t)
                  in
               match uu____27595 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27617  ->
                         let uu____27618 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27620 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27618 uu____27620);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27639 =
          let uu____27643 =
            let uu____27645 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____27645  in
          FStar_Pervasives_Native.Some uu____27643  in
        FStar_Profiling.profile
          (fun uu____27648  -> normalize_with_primitive_steps [] s e t)
          uu____27639 "FStar.TypeChecker.Normalize"
  
let (normalize_comp :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun c  ->
        let cfg = FStar_TypeChecker_Cfg.config s e  in
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27670  ->
             let uu____27671 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27671);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27677  ->
             let uu____27678 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27678);
        (let uu____27681 =
           FStar_Util.record_time (fun uu____27688  -> norm_comp cfg [] c)
            in
         match uu____27681 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27703  ->
                   let uu____27704 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____27706 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27704
                     uu____27706);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27720 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____27720 [] u
  
let (non_info_norm :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.AllowUnboundUniverses;
        FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.HNF;
        FStar_TypeChecker_Env.Unascribe;
        FStar_TypeChecker_Env.ForExtraction]  in
      let uu____27742 = normalize steps env t  in
      FStar_TypeChecker_Env.non_informative env uu____27742
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27754 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env t ->
          let uu___3252_27773 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3252_27773.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3252_27773.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27780 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27780
          then
            let ct1 =
              let uu____27784 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27784 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____27791 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27791
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3262_27798 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3262_27798.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3262_27798.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3262_27798.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c
                     in
                  let uu___3266_27800 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3266_27800.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3266_27800.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3266_27800.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3266_27800.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3269_27801 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3269_27801.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3269_27801.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27804 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      let uu____27816 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____27816
      then
        let uu____27819 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____27819 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3277_27823 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3277_27823.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3277_27823.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3277_27823.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3284_27842  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3283_27845 ->
            ((let uu____27847 =
                let uu____27853 =
                  let uu____27855 = FStar_Util.message_of_exn uu___3283_27845
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27855
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27853)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27847);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3294_27874  ->
             match () with
             | () ->
                 let uu____27875 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____27875 [] c) ()
        with
        | uu___3293_27884 ->
            ((let uu____27886 =
                let uu____27892 =
                  let uu____27894 = FStar_Util.message_of_exn uu___3293_27884
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27894
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27892)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27886);
             c)
         in
      FStar_Syntax_Print.comp_to_string' env.FStar_TypeChecker_Env.dsenv c1
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let t =
          normalize (FStar_List.append steps [FStar_TypeChecker_Env.Beta])
            env t0
           in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1  in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort  in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____27943 =
                     let uu____27944 =
                       let uu____27951 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27951)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27944  in
                   mk uu____27943 t01.FStar_Syntax_Syntax.pos
               | uu____27956 -> t2)
          | uu____27957 -> t2  in
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
  fun steps  ->
    fun env  ->
      fun t  -> normalize (FStar_List.append steps whnf_steps) env t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> unfold_whnf' [] env t 
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun remove  ->
    fun env  ->
      fun t  ->
        normalize
          (FStar_List.append
             (if remove then [FStar_TypeChecker_Env.CheckNoUvars] else [])
             [FStar_TypeChecker_Env.Beta;
             FStar_TypeChecker_Env.DoNotUnfoldPureLets;
             FStar_TypeChecker_Env.CompressUvars;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
             FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Iota;
             FStar_TypeChecker_Env.NoFullNorm]) env t
  
let (reduce_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions false env t 
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env  -> fun t  -> reduce_or_remove_uvar_solutions true env t 
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      fun t_e  ->
        let uu____28051 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____28051 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____28064 ->
                 let uu____28065 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____28065 with
                  | (actuals,uu____28075,uu____28076) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____28096 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____28096 with
                         | (binders,args) ->
                             let uu____28107 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____28107
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env t x.FStar_Syntax_Syntax.sort
      | uu____28122 ->
          let uu____28123 = FStar_Syntax_Util.head_and_args t  in
          (match uu____28123 with
           | (head1,args) ->
               let uu____28166 =
                 let uu____28167 = FStar_Syntax_Subst.compress head1  in
                 uu____28167.FStar_Syntax_Syntax.n  in
               (match uu____28166 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____28188 =
                      let uu____28195 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____28195  in
                    (match uu____28188 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____28219 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3364_28227 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3364_28227.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3364_28227.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3364_28227.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3364_28227.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3364_28227.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3364_28227.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3364_28227.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3364_28227.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3364_28227.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3364_28227.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3364_28227.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3364_28227.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3364_28227.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3364_28227.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3364_28227.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3364_28227.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3364_28227.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3364_28227.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3364_28227.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3364_28227.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3364_28227.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3364_28227.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3364_28227.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3364_28227.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3364_28227.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3364_28227.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3364_28227.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3364_28227.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3364_28227.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3364_28227.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3364_28227.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3364_28227.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3364_28227.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3364_28227.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3364_28227.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3364_28227.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3364_28227.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3364_28227.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3364_28227.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3364_28227.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3364_28227.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3364_28227.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3364_28227.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3364_28227.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____28219 with
                            | (uu____28230,ty,uu____28232) ->
                                eta_expand_with_type env t ty))
                | uu____28233 ->
                    let uu____28234 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3371_28242 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3371_28242.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3371_28242.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3371_28242.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3371_28242.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3371_28242.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3371_28242.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3371_28242.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3371_28242.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3371_28242.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3371_28242.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3371_28242.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3371_28242.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3371_28242.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3371_28242.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3371_28242.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3371_28242.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3371_28242.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3371_28242.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3371_28242.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3371_28242.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3371_28242.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3371_28242.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3371_28242.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3371_28242.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3371_28242.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3371_28242.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3371_28242.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3371_28242.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3371_28242.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3371_28242.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3371_28242.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3371_28242.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3371_28242.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3371_28242.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3371_28242.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3371_28242.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3371_28242.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3371_28242.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3371_28242.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3371_28242.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3371_28242.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3371_28242.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3371_28242.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3371_28242.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____28234 with
                     | (uu____28245,ty,uu____28247) ->
                         eta_expand_with_type env t ty)))
  
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
       in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___3383_28329 = x  in
      let uu____28330 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3383_28329.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3383_28329.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28330
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28333 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28349 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28350 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28351 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28352 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28359 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28360 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28361 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3409_28395 = rc  in
          let uu____28396 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28405 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3409_28395.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28396;
            FStar_Syntax_Syntax.residual_flags = uu____28405
          }  in
        let uu____28408 =
          let uu____28409 =
            let uu____28428 = elim_delayed_subst_binders bs  in
            let uu____28437 = elim_delayed_subst_term t2  in
            let uu____28440 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28428, uu____28437, uu____28440)  in
          FStar_Syntax_Syntax.Tm_abs uu____28409  in
        mk1 uu____28408
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28477 =
          let uu____28478 =
            let uu____28493 = elim_delayed_subst_binders bs  in
            let uu____28502 = elim_delayed_subst_comp c  in
            (uu____28493, uu____28502)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28478  in
        mk1 uu____28477
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28521 =
          let uu____28522 =
            let uu____28529 = elim_bv bv  in
            let uu____28530 = elim_delayed_subst_term phi  in
            (uu____28529, uu____28530)  in
          FStar_Syntax_Syntax.Tm_refine uu____28522  in
        mk1 uu____28521
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28561 =
          let uu____28562 =
            let uu____28579 = elim_delayed_subst_term t2  in
            let uu____28582 = elim_delayed_subst_args args  in
            (uu____28579, uu____28582)  in
          FStar_Syntax_Syntax.Tm_app uu____28562  in
        mk1 uu____28561
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3431_28654 = p  in
              let uu____28655 =
                let uu____28656 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28656  in
              {
                FStar_Syntax_Syntax.v = uu____28655;
                FStar_Syntax_Syntax.p =
                  (uu___3431_28654.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3435_28658 = p  in
              let uu____28659 =
                let uu____28660 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28660  in
              {
                FStar_Syntax_Syntax.v = uu____28659;
                FStar_Syntax_Syntax.p =
                  (uu___3435_28658.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3441_28667 = p  in
              let uu____28668 =
                let uu____28669 =
                  let uu____28676 = elim_bv x  in
                  let uu____28677 = elim_delayed_subst_term t0  in
                  (uu____28676, uu____28677)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28669  in
              {
                FStar_Syntax_Syntax.v = uu____28668;
                FStar_Syntax_Syntax.p =
                  (uu___3441_28667.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3447_28702 = p  in
              let uu____28703 =
                let uu____28704 =
                  let uu____28718 =
                    FStar_List.map
                      (fun uu____28744  ->
                         match uu____28744 with
                         | (x,b) ->
                             let uu____28761 = elim_pat x  in
                             (uu____28761, b)) pats
                     in
                  (fv, uu____28718)  in
                FStar_Syntax_Syntax.Pat_cons uu____28704  in
              {
                FStar_Syntax_Syntax.v = uu____28703;
                FStar_Syntax_Syntax.p =
                  (uu___3447_28702.FStar_Syntax_Syntax.p)
              }
          | uu____28776 -> p  in
        let elim_branch uu____28800 =
          match uu____28800 with
          | (pat,wopt,t3) ->
              let uu____28826 = elim_pat pat  in
              let uu____28829 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28832 = elim_delayed_subst_term t3  in
              (uu____28826, uu____28829, uu____28832)
           in
        let uu____28837 =
          let uu____28838 =
            let uu____28861 = elim_delayed_subst_term t2  in
            let uu____28864 = FStar_List.map elim_branch branches  in
            (uu____28861, uu____28864)  in
          FStar_Syntax_Syntax.Tm_match uu____28838  in
        mk1 uu____28837
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28995 =
          match uu____28995 with
          | (tc,topt) ->
              let uu____29030 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____29040 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____29040
                | FStar_Util.Inr c ->
                    let uu____29042 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____29042
                 in
              let uu____29043 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____29030, uu____29043)
           in
        let uu____29052 =
          let uu____29053 =
            let uu____29080 = elim_delayed_subst_term t2  in
            let uu____29083 = elim_ascription a  in
            (uu____29080, uu____29083, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____29053  in
        mk1 uu____29052
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3477_29146 = lb  in
          let uu____29147 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____29150 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3477_29146.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3477_29146.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____29147;
            FStar_Syntax_Syntax.lbeff =
              (uu___3477_29146.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____29150;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3477_29146.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3477_29146.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____29153 =
          let uu____29154 =
            let uu____29168 =
              let uu____29176 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____29176)  in
            let uu____29188 = elim_delayed_subst_term t2  in
            (uu____29168, uu____29188)  in
          FStar_Syntax_Syntax.Tm_let uu____29154  in
        mk1 uu____29153
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____29233 =
          let uu____29234 =
            let uu____29241 = elim_delayed_subst_term tm  in
            (uu____29241, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____29234  in
        mk1 uu____29233
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29252 =
          let uu____29253 =
            let uu____29260 = elim_delayed_subst_term t2  in
            let uu____29263 = elim_delayed_subst_meta md  in
            (uu____29260, uu____29263)  in
          FStar_Syntax_Syntax.Tm_meta uu____29253  in
        mk1 uu____29252

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29272  ->
         match uu___17_29272 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29276 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29276
         | f -> f) flags

and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        c.FStar_Syntax_Syntax.pos
       in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____29299 =
          let uu____29300 =
            let uu____29309 = elim_delayed_subst_term t  in
            (uu____29309, uopt)  in
          FStar_Syntax_Syntax.Total uu____29300  in
        mk1 uu____29299
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29326 =
          let uu____29327 =
            let uu____29336 = elim_delayed_subst_term t  in
            (uu____29336, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29327  in
        mk1 uu____29326
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3510_29345 = ct  in
          let uu____29346 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29349 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29360 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3510_29345.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3510_29345.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29346;
            FStar_Syntax_Syntax.effect_args = uu____29349;
            FStar_Syntax_Syntax.flags = uu____29360
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29363  ->
    match uu___18_29363 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____29398 =
          let uu____29419 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____29428 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29419, uu____29428)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29398
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____29483 =
          let uu____29490 = elim_delayed_subst_term t  in (m, uu____29490)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____29483
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____29502 =
          let uu____29511 = elim_delayed_subst_term t  in
          (m1, m2, uu____29511)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29502
    | m -> m

and (elim_delayed_subst_args :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
    Prims.list ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list)
  =
  fun args  ->
    FStar_List.map
      (fun uu____29544  ->
         match uu____29544 with
         | (t,q) ->
             let uu____29563 = elim_delayed_subst_term t  in (uu____29563, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29591  ->
         match uu____29591 with
         | (x,q) ->
             let uu____29610 =
               let uu___3536_29611 = x  in
               let uu____29612 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3536_29611.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3536_29611.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29612
               }  in
             (uu____29610, q)) bs

let (elim_uvars_aux_tc :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.univ_names ->
      FStar_Syntax_Syntax.binders ->
        (FStar_Syntax_Syntax.typ,FStar_Syntax_Syntax.comp) FStar_Util.either
          ->
          (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list *
            (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.comp'
                                                                    FStar_Syntax_Syntax.syntax)
            FStar_Util.either))
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
            | (uu____29720,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29752,FStar_Util.Inl t) ->
                let uu____29774 =
                  let uu____29781 =
                    let uu____29782 =
                      let uu____29797 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29797)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29782  in
                  FStar_Syntax_Syntax.mk uu____29781  in
                uu____29774 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29810 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29810 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29842 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29915 ->
                    let uu____29916 =
                      let uu____29925 =
                        let uu____29926 = FStar_Syntax_Subst.compress t4  in
                        uu____29926.FStar_Syntax_Syntax.n  in
                      (uu____29925, tc)  in
                    (match uu____29916 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29955) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____30002) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____30047,FStar_Util.Inl uu____30048) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____30079 -> failwith "Impossible")
                 in
              (match uu____29842 with
               | (binders1,tc1) -> (univ_names1, binders1, tc1))
  
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
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____30218 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____30218 with
          | (univ_names1,binders1,tc) ->
              let uu____30292 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30292)
  
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
  fun env  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____30346 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____30346 with
          | (univ_names1,binders1,tc) ->
              let uu____30420 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30420)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____30462 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____30462 with
           | (univ_names1,binders1,typ1) ->
               let uu___3619_30502 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3619_30502.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3619_30502.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3619_30502.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3619_30502.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3619_30502.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3625_30517 = s  in
          let uu____30518 =
            let uu____30519 =
              let uu____30528 = FStar_List.map (elim_uvars env) sigs  in
              (uu____30528, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____30519  in
          {
            FStar_Syntax_Syntax.sigel = uu____30518;
            FStar_Syntax_Syntax.sigrng =
              (uu___3625_30517.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3625_30517.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3625_30517.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3625_30517.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3625_30517.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____30547 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30547 with
           | (univ_names1,uu____30571,typ1) ->
               let uu___3639_30593 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3639_30593.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3639_30593.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3639_30593.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3639_30593.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3639_30593.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____30600 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30600 with
           | (univ_names1,uu____30624,typ1) ->
               let uu___3650_30646 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3650_30646.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3650_30646.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3650_30646.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3650_30646.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3650_30646.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30676 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30676 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____30701 =
                            let uu____30702 =
                              let uu____30703 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____30703  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30702
                             in
                          elim_delayed_subst_term uu____30701  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3666_30706 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3666_30706.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3666_30706.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3666_30706.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3666_30706.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3669_30707 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3669_30707.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3669_30707.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3669_30707.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3669_30707.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3669_30707.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3673_30714 = s  in
          let uu____30715 =
            let uu____30716 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____30716  in
          {
            FStar_Syntax_Syntax.sigel = uu____30715;
            FStar_Syntax_Syntax.sigrng =
              (uu___3673_30714.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3673_30714.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3673_30714.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3673_30714.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3673_30714.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____30720 = elim_uvars_aux_t env us [] t  in
          (match uu____30720 with
           | (us1,uu____30744,t1) ->
               let uu___3684_30766 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3684_30766.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3684_30766.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3684_30766.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3684_30766.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3684_30766.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30768 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____30768 with
           | (univs1,binders,uu____30787) ->
               let uu____30808 =
                 let uu____30813 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____30813 with
                 | (univs_opening,univs2) ->
                     let uu____30836 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____30836)
                  in
               (match uu____30808 with
                | (univs_opening,univs_closing) ->
                    let uu____30839 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30845 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30846 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30845, uu____30846)  in
                    (match uu____30839 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30872 =
                           match uu____30872 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30890 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30890 with
                                | (us1,t1) ->
                                    let uu____30901 =
                                      let uu____30910 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30915 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30910, uu____30915)  in
                                    (match uu____30901 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30938 =
                                           let uu____30947 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____30952 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____30947, uu____30952)  in
                                         (match uu____30938 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30976 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30976
                                                 in
                                              let uu____30977 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30977 with
                                               | (uu____31004,uu____31005,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____31028 =
                                                       let uu____31029 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____31029
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____31028
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____31038 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____31038 with
                           | (uu____31057,uu____31058,t1) -> t1  in
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
                                 FStar_Pervasives_Native.None
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____31134 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____31161 =
                               let uu____31162 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____31162.FStar_Syntax_Syntax.n  in
                             match uu____31161 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____31221 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31255 =
                               let uu____31256 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31256.FStar_Syntax_Syntax.n  in
                             match uu____31255 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31279) ->
                                 let uu____31304 = destruct_action_body body
                                    in
                                 (match uu____31304 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31353 ->
                                 let uu____31354 = destruct_action_body t  in
                                 (match uu____31354 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31409 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31409 with
                           | (action_univs,t) ->
                               let uu____31418 = destruct_action_typ_templ t
                                  in
                               (match uu____31418 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3768_31465 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3768_31465.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3768_31465.FStar_Syntax_Syntax.action_unqualified_name);
                                        FStar_Syntax_Syntax.action_univs =
                                          action_univs;
                                        FStar_Syntax_Syntax.action_params =
                                          action_params;
                                        FStar_Syntax_Syntax.action_defn =
                                          action_defn;
                                        FStar_Syntax_Syntax.action_typ =
                                          action_typ
                                      }  in
                                    a')
                            in
                         let ed1 =
                           let uu___3771_31467 = ed  in
                           let uu____31468 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____31469 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____31470 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3771_31467.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3771_31467.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31468;
                             FStar_Syntax_Syntax.combinators = uu____31469;
                             FStar_Syntax_Syntax.actions = uu____31470;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3771_31467.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3774_31473 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3774_31473.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3774_31473.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3774_31473.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3774_31473.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3774_31473.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31494 =
            match uu___19_31494 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____31525 = elim_uvars_aux_t env us [] t  in
                (match uu____31525 with
                 | (us1,uu____31557,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3789_31588 = sub_eff  in
            let uu____31589 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____31592 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3789_31588.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3789_31588.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31589;
              FStar_Syntax_Syntax.lift = uu____31592
            }  in
          let uu___3792_31595 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3792_31595.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3792_31595.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3792_31595.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3792_31595.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3792_31595.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____31605 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____31605 with
           | (univ_names1,binders1,comp1) ->
               let uu___3805_31645 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3805_31645.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3805_31645.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3805_31645.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3805_31645.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3805_31645.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31648 -> s
      | FStar_Syntax_Syntax.Sig_fail uu____31649 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31662 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n1,p,(us_t,t),(us_ty,ty))
          ->
          let uu____31692 = elim_uvars_aux_t env us_t [] t  in
          (match uu____31692 with
           | (us_t1,uu____31716,t1) ->
               let uu____31738 = elim_uvars_aux_t env us_ty [] ty  in
               (match uu____31738 with
                | (us_ty1,uu____31762,ty1) ->
                    let uu___3832_31784 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n1, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3832_31784.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3832_31784.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3832_31784.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3832_31784.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3832_31784.FStar_Syntax_Syntax.sigopts)
                    }))
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env t
  
let (unfold_head_once :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let aux f us args =
        let uu____31835 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____31835 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____31857 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____31857 with
             | (uu____31864,head_def) ->
                 let t' =
                   FStar_Syntax_Syntax.mk_Tm_app head_def args
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                    in
                 let t'1 =
                   normalize
                     [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota]
                     env t'
                    in
                 FStar_Pervasives_Native.Some t'1)
         in
      let uu____31870 = FStar_Syntax_Util.head_and_args t  in
      match uu____31870 with
      | (head1,args) ->
          let uu____31915 =
            let uu____31916 = FStar_Syntax_Subst.compress head1  in
            uu____31916.FStar_Syntax_Syntax.n  in
          (match uu____31915 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31923;
                  FStar_Syntax_Syntax.vars = uu____31924;_},us)
               -> aux fv us args
           | uu____31930 -> FStar_Pervasives_Native.None)
  