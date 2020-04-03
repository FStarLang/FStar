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
                     ((let uu____10369 =
                         FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                       FStar_Util.print1
                         ">>>>>>>Norm request with cfg = %s\n" uu____10369);
                      norm cfg'1 env stack' tm)))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10374 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10374
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10385 =
                      let uu____10392 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10392, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10385  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10401 = lookup_bvar env x  in
               (match uu____10401 with
                | Univ uu____10402 ->
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
                      let uu____10456 = FStar_ST.op_Bang r  in
                      (match uu____10456 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10552  ->
                                 let uu____10553 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10555 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10553
                                   uu____10555);
                            (let uu____10558 = maybe_weakly_reduced t'  in
                             if uu____10558
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____10561 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10605)::uu____10606 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10617,uu____10618))::stack_rest ->
                    (match c with
                     | Univ uu____10622 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10631 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10661  ->
                                    let uu____10662 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10662);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10698  ->
                                    let uu____10699 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10699);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl1, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env) stack_rest body1))))
                | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                | (MemoLazy r)::stack1 ->
                    (set_memo cfg r (env, t1);
                     FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10747  ->
                          let uu____10748 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10748);
                     norm cfg env stack1 t1)
                | (Match uu____10751)::uu____10752 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10767 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10767 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10803  -> dummy :: env1) env)
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
                                          let uu____10847 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10847)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1443_10855 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1443_10855.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1443_10855.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10856 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10862  ->
                                 let uu____10863 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10863);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1450_10878 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1450_10878.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1450_10878.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1450_10878.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1450_10878.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1450_10878.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1450_10878.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1450_10878.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1450_10878.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____10882)::uu____10883 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10894 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10894 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10930  -> dummy :: env1) env)
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
                                          let uu____10974 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10974)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1443_10982 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1443_10982.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1443_10982.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10983 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10989  ->
                                 let uu____10990 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10990);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1450_11005 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1450_11005.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1450_11005.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1450_11005.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1450_11005.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1450_11005.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1450_11005.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1450_11005.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1450_11005.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____11009)::uu____11010 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11023 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11023 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11059  -> dummy :: env1) env)
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
                                          let uu____11103 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11103)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1443_11111 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1443_11111.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1443_11111.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11112 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11118  ->
                                 let uu____11119 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11119);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1450_11134 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1450_11134.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1450_11134.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1450_11134.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1450_11134.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1450_11134.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1450_11134.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1450_11134.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1450_11134.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11138)::uu____11139 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11154 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11154 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11190  -> dummy :: env1) env)
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
                                          let uu____11234 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11234)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1443_11242 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1443_11242.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1443_11242.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11243 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11249  ->
                                 let uu____11250 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11250);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1450_11265 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1450_11265.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1450_11265.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1450_11265.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1450_11265.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1450_11265.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1450_11265.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1450_11265.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1450_11265.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11269)::uu____11270 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11285 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11285 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11321  -> dummy :: env1) env)
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
                                          let uu____11365 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11365)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1443_11373 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1443_11373.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1443_11373.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11374 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11380  ->
                                 let uu____11381 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11381);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1450_11396 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1450_11396.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1450_11396.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1450_11396.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1450_11396.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1450_11396.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1450_11396.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1450_11396.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1450_11396.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (CBVApp uu____11400)::uu____11401 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11416 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11416 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11452  -> dummy :: env1) env)
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
                                          let uu____11496 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11496)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1443_11504 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1443_11504.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1443_11504.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11505 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11511  ->
                                 let uu____11512 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11512);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1450_11527 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1450_11527.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1450_11527.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1450_11527.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1450_11527.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1450_11527.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1450_11527.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1450_11527.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1450_11527.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11531)::uu____11532 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11551 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11551 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11587  -> dummy :: env1) env)
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
                                          let uu____11631 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11631)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1443_11639 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1443_11639.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1443_11639.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11640 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11646  ->
                                 let uu____11647 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11647);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1450_11662 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1450_11662.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1450_11662.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1450_11662.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1450_11662.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1450_11662.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1450_11662.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1450_11662.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1450_11662.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____11670 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11670 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11706  -> dummy :: env1) env)
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
                                          let uu____11750 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11750)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1443_11758 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1443_11758.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1443_11758.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11759 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11765  ->
                                 let uu____11766 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11766);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1450_11781 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1450_11781.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1450_11781.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1450_11781.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1450_11781.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1450_11781.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1450_11781.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1450_11781.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1450_11781.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let strict_args =
                 let uu____11817 =
                   let uu____11818 = FStar_Syntax_Util.un_uinst head1  in
                   uu____11818.FStar_Syntax_Syntax.n  in
                 match uu____11817 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11827 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11848  ->
                              fun stack1  ->
                                match uu____11848 with
                                | (a,aq) ->
                                    let uu____11860 =
                                      let uu____11861 =
                                        let uu____11868 =
                                          let uu____11869 =
                                            let uu____11901 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11901, false)  in
                                          Clos uu____11869  in
                                        (uu____11868, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11861  in
                                    uu____11860 :: stack1) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11969  ->
                          let uu____11970 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11970);
                     norm cfg env stack1 head1)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____12021  ->
                              match uu____12021 with
                              | (a,i) ->
                                  let uu____12032 = norm cfg env [] a  in
                                  (uu____12032, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____12038 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____12053 = FStar_List.nth norm_args i
                                    in
                                 match uu____12053 with
                                 | (arg_i,uu____12064) ->
                                     let uu____12065 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____12065 with
                                      | (head2,uu____12084) ->
                                          let uu____12109 =
                                            let uu____12110 =
                                              FStar_Syntax_Util.un_uinst
                                                head2
                                               in
                                            uu____12110.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____12109 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____12114 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____12117 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____12117
                                           | uu____12118 -> false)))))
                       in
                    if uu____12038
                    then
                      let stack1 =
                        FStar_All.pipe_right stack
                          (FStar_List.fold_right
                             (fun uu____12135  ->
                                fun stack1  ->
                                  match uu____12135 with
                                  | (a,aq) ->
                                      let uu____12147 =
                                        let uu____12148 =
                                          let uu____12155 =
                                            let uu____12156 =
                                              let uu____12188 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env, a, uu____12188, false)
                                               in
                                            Clos uu____12156  in
                                          (uu____12155, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____12148  in
                                      uu____12147 :: stack1) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12270  ->
                            let uu____12271 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12271);
                       norm cfg env stack1 head1)
                    else
                      (let head2 = closure_as_term cfg env head1  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                           FStar_Pervasives_Native.None
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env stack term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12291) when
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
                             ((let uu___1512_12336 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1512_12336.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1512_12336.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12337 ->
                      let uu____12352 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12352)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12356 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12356 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12387 =
                          let uu____12388 =
                            let uu____12395 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1521_12401 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1521_12401.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1521_12401.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12395)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12388  in
                        mk uu____12387 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12425 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12425
               else
                 (let uu____12428 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12428 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12436 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12462  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12436 c1  in
                      let t2 =
                        let uu____12486 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12486 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12599)::uu____12600 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12613  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12615)::uu____12616 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12627  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12629,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12630;
                                   FStar_Syntax_Syntax.vars = uu____12631;_},uu____12632,uu____12633))::uu____12634
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12641  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12643)::uu____12644 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12655  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12657 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12660  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12665  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12691 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12691
                         | FStar_Util.Inr c ->
                             let uu____12705 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12705
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12728 =
                               let uu____12729 =
                                 let uu____12756 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12756, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12729
                                in
                             mk uu____12728 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12791 ->
                           let uu____12792 =
                             let uu____12793 =
                               let uu____12794 =
                                 let uu____12821 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12821, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12794
                                in
                             mk uu____12793 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12792))))
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
                   let uu___1600_12899 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1602_12902 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1602_12902.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1600_12899.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1600_12899.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1600_12899.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1600_12899.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1600_12899.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1600_12899.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1600_12899.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1600_12899.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____12943 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12943 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1615_12963 = cfg  in
                               let uu____12964 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1615_12963.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12964;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1615_12963.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1615_12963.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1615_12963.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1615_12963.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1615_12963.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1615_12963.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1615_12963.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____12971 =
                                 let uu____12972 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12972  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12971
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1622_12975 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1622_12975.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1622_12975.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1622_12975.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1622_12975.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12976 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12976
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12989,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12990;
                               FStar_Syntax_Syntax.lbunivs = uu____12991;
                               FStar_Syntax_Syntax.lbtyp = uu____12992;
                               FStar_Syntax_Syntax.lbeff = uu____12993;
                               FStar_Syntax_Syntax.lbdef = uu____12994;
                               FStar_Syntax_Syntax.lbattrs = uu____12995;
                               FStar_Syntax_Syntax.lbpos = uu____12996;_}::uu____12997),uu____12998)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let uu____13043 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
               if uu____13043
               then
                 let binder =
                   let uu____13047 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13047  in
                 let env1 =
                   let uu____13057 =
                     let uu____13064 =
                       let uu____13065 =
                         let uu____13097 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____13097,
                           false)
                          in
                       Clos uu____13065  in
                     ((FStar_Pervasives_Native.Some binder), uu____13064)  in
                   uu____13057 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____13172  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 (let uu____13176 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu____13179 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff
                          in
                       FStar_Syntax_Util.is_div_effect uu____13179)
                     in
                  if uu____13176
                  then
                    let ffun =
                      let uu____13184 =
                        let uu____13191 =
                          let uu____13192 =
                            let uu____13211 =
                              let uu____13220 =
                                let uu____13227 =
                                  FStar_All.pipe_right
                                    lb.FStar_Syntax_Syntax.lbname
                                    FStar_Util.left
                                   in
                                FStar_Syntax_Syntax.mk_binder uu____13227  in
                              [uu____13220]  in
                            (uu____13211, body, FStar_Pervasives_Native.None)
                             in
                          FStar_Syntax_Syntax.Tm_abs uu____13192  in
                        FStar_Syntax_Syntax.mk uu____13191  in
                      uu____13184 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    let stack1 =
                      (CBVApp
                         (env, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____13261  ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env stack1 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____13268  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____13270 = closure_as_term cfg env t1  in
                        rebuild cfg env stack uu____13270))
                    else
                      (let uu____13273 =
                         let uu____13278 =
                           let uu____13279 =
                             let uu____13286 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____13286
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____13279]  in
                         FStar_Syntax_Subst.open_term uu____13278 body  in
                       match uu____13273 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____13313  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____13322 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____13322  in
                               FStar_Util.Inl
                                 (let uu___1668_13338 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1668_13338.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1668_13338.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____13341  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1673_13344 = lb  in
                                let uu____13345 =
                                  norm cfg env []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____13348 =
                                  FStar_List.map (norm cfg env [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1673_13344.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1673_13344.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____13345;
                                  FStar_Syntax_Syntax.lbattrs = uu____13348;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1673_13344.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____13383  -> dummy :: env1)
                                     env)
                                 in
                              let stack1 = (Cfg cfg) :: stack  in
                              let cfg1 =
                                let uu___1680_13408 = cfg  in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1680_13408.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1680_13408.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1680_13408.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1680_13408.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1680_13408.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1680_13408.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1680_13408.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1680_13408.FStar_TypeChecker_Cfg.reifying)
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____13412  ->
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
               let uu____13433 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13433 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13469 =
                               let uu___1696_13470 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1696_13470.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1696_13470.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13469  in
                           let uu____13471 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13471 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13497 =
                                   FStar_List.map (fun uu____13519  -> dummy)
                                     xs1
                                    in
                                 let uu____13526 =
                                   let uu____13535 =
                                     FStar_List.map
                                       (fun uu____13551  -> dummy) lbs1
                                      in
                                   FStar_List.append uu____13535 env  in
                                 FStar_List.append uu____13497 uu____13526
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13571 =
                                       let uu___1710_13572 = rc  in
                                       let uu____13573 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1710_13572.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13573;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1710_13572.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13571
                                 | uu____13582 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1715_13588 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1715_13588.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1715_13588.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1715_13588.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1715_13588.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13598 =
                        FStar_List.map (fun uu____13614  -> dummy) lbs2  in
                      FStar_List.append uu____13598 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13622 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13622 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1724_13638 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1724_13638.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1724_13638.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu____13672 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13672
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13693 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13771  ->
                        match uu____13771 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1740_13896 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1740_13896.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1740_13896.FStar_Syntax_Syntax.sort)
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
               (match uu____13693 with
                | (rec_env,memos,uu____14087) ->
                    let uu____14142 =
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
                             let uu____14391 =
                               let uu____14398 =
                                 let uu____14399 =
                                   let uu____14431 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14431, false)
                                    in
                                 Clos uu____14399  in
                               (FStar_Pervasives_Native.None, uu____14398)
                                in
                             uu____14391 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14516  ->
                     let uu____14517 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14517);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14541 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14545::uu____14546 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14551) ->
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
                             | uu____14630 -> norm cfg env stack head1)
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
                                  let uu____14678 =
                                    let uu____14699 =
                                      norm_pattern_args cfg env args  in
                                    (names2, uu____14699)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14678
                              | uu____14728 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14734 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14750 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14764 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14778 =
                        let uu____14780 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14782 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14780 uu____14782
                         in
                      failwith uu____14778
                    else
                      (let uu____14787 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____14787)
                | uu____14788 -> norm cfg env stack t2))

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
              let uu____14797 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14797 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14811  ->
                        let uu____14812 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14812);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14825  ->
                        let uu____14826 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14828 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14826 uu____14828);
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
                      | (UnivArgs (us',uu____14841))::stack1 ->
                          ((let uu____14850 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14850
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14858 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14858) us'
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
                      | uu____14894 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14897 ->
                          let uu____14900 =
                            let uu____14902 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14902
                             in
                          failwith uu____14900
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
              let uu____14922 =
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
                    let uu___1851_14940 = cfg  in
                    let uu____14941 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps
                       in
                    {
                      FStar_TypeChecker_Cfg.steps = uu____14941;
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1851_14940.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1851_14940.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        [FStar_TypeChecker_Env.InliningDelta;
                        FStar_TypeChecker_Env.Eager_unfolding_only];
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1851_14940.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1851_14940.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1851_14940.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1851_14940.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1851_14940.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  (cfg', ((Cfg cfg) :: stack))
                else (cfg, stack)  in
              match uu____14922 with
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
                     (uu____14982,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14983;
                                    FStar_Syntax_Syntax.vars = uu____14984;_},uu____14985,uu____14986))::uu____14987
                     -> ()
                 | uu____14992 ->
                     let uu____14995 =
                       let uu____14997 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14997
                        in
                     failwith uu____14995);
                (let top0 = top  in
                 let top1 = FStar_Syntax_Util.unascribe top  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____15006  ->
                      let uu____15007 = FStar_Syntax_Print.tag_of_term top1
                         in
                      let uu____15009 =
                        FStar_Syntax_Print.term_to_string top1  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____15007
                        uu____15009);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1  in
                  let uu____15013 =
                    let uu____15014 = FStar_Syntax_Subst.compress top2  in
                    uu____15014.FStar_Syntax_Syntax.n  in
                  match uu____15013 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m
                         in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name
                         in
                      let uu____15036 =
                        let uu____15045 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr
                           in
                        FStar_All.pipe_right uu____15045 FStar_Util.must  in
                      (match uu____15036 with
                       | (uu____15060,repr) ->
                           let uu____15070 =
                             let uu____15077 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr
                                in
                             FStar_All.pipe_right uu____15077 FStar_Util.must
                              in
                           (match uu____15070 with
                            | (uu____15114,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15120 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15131 =
                                         let uu____15132 =
                                           FStar_Syntax_Subst.compress e  in
                                         uu____15132.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15131 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15138,uu____15139))
                                           ->
                                           let uu____15148 =
                                             let uu____15149 =
                                               FStar_Syntax_Subst.compress e1
                                                in
                                             uu____15149.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____15148 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15155,msrc,uu____15157))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15166 =
                                                  FStar_Syntax_Subst.compress
                                                    e2
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____15166
                                            | uu____15167 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15168 ->
                                           FStar_Pervasives_Native.None
                                        in
                                     let uu____15169 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     (match uu____15169 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___1930_15174 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___1930_15174.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___1930_15174.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___1930_15174.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e;
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___1930_15174.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___1930_15174.FStar_Syntax_Syntax.lbpos)
                                            }  in
                                          let uu____15175 =
                                            FStar_List.tl stack  in
                                          let uu____15176 =
                                            let uu____15177 =
                                              let uu____15184 =
                                                let uu____15185 =
                                                  let uu____15199 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body
                                                     in
                                                  ((false, [lb1]),
                                                    uu____15199)
                                                   in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15185
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15184
                                               in
                                            uu____15177
                                              FStar_Pervasives_Native.None
                                              top2.FStar_Syntax_Syntax.pos
                                             in
                                          norm cfg env uu____15175
                                            uu____15176
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15215 =
                                            let uu____15217 = is_return body
                                               in
                                            match uu____15217 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15222;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15223;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15226 -> false  in
                                          if uu____15215
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
                                             let uu____15241 =
                                               let bv =
                                                 FStar_Syntax_Syntax.new_bv
                                                   FStar_Pervasives_Native.None
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let lb1 =
                                                 let uu____15250 =
                                                   let uu____15253 =
                                                     let uu____15264 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         x.FStar_Syntax_Syntax.sort
                                                        in
                                                     [uu____15264]  in
                                                   FStar_Syntax_Util.mk_app
                                                     repr uu____15253
                                                    in
                                                 let uu____15289 =
                                                   let uu____15290 =
                                                     FStar_TypeChecker_Env.is_total_effect
                                                       cfg.FStar_TypeChecker_Cfg.tcenv
                                                       eff_name
                                                      in
                                                   if uu____15290
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
                                                     = uu____15250;
                                                   FStar_Syntax_Syntax.lbeff
                                                     = uu____15289;
                                                   FStar_Syntax_Syntax.lbdef
                                                     = head1;
                                                   FStar_Syntax_Syntax.lbattrs
                                                     = [];
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (head1.FStar_Syntax_Syntax.pos)
                                                 }  in
                                               let uu____15297 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   bv
                                                  in
                                               (lb1, bv, uu____15297)  in
                                             match uu____15241 with
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
                                                   let uu____15314 =
                                                     let uu____15321 =
                                                       let uu____15322 =
                                                         let uu____15341 =
                                                           let uu____15350 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x
                                                              in
                                                           [uu____15350]  in
                                                         (uu____15341, body1,
                                                           (FStar_Pervasives_Native.Some
                                                              body_rc))
                                                          in
                                                       FStar_Syntax_Syntax.Tm_abs
                                                         uu____15322
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15321
                                                      in
                                                   uu____15314
                                                     FStar_Pervasives_Native.None
                                                     body1.FStar_Syntax_Syntax.pos
                                                    in
                                                 let close1 =
                                                   closure_as_term cfg env
                                                    in
                                                 let bind_inst =
                                                   let uu____15389 =
                                                     let uu____15390 =
                                                       FStar_Syntax_Subst.compress
                                                         bind_repr
                                                        in
                                                     uu____15390.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____15389 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (bind1,uu____15396::uu____15397::[])
                                                       ->
                                                       let uu____15402 =
                                                         let uu____15409 =
                                                           let uu____15410 =
                                                             let uu____15417
                                                               =
                                                               let uu____15418
                                                                 =
                                                                 let uu____15419
                                                                   =
                                                                   close1
                                                                    lb.FStar_Syntax_Syntax.lbtyp
                                                                    in
                                                                 (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                                   uu____15419
                                                                  in
                                                               let uu____15420
                                                                 =
                                                                 let uu____15423
                                                                   =
                                                                   let uu____15424
                                                                    =
                                                                    close1 t
                                                                     in
                                                                   (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                    cfg.FStar_TypeChecker_Cfg.tcenv
                                                                    uu____15424
                                                                    in
                                                                 [uu____15423]
                                                                  in
                                                               uu____15418 ::
                                                                 uu____15420
                                                                in
                                                             (bind1,
                                                               uu____15417)
                                                              in
                                                           FStar_Syntax_Syntax.Tm_uinst
                                                             uu____15410
                                                            in
                                                         FStar_Syntax_Syntax.mk
                                                           uu____15409
                                                          in
                                                       uu____15402
                                                         FStar_Pervasives_Native.None
                                                         rng
                                                   | uu____15427 ->
                                                       failwith
                                                         "NIY : Reification of indexed effects"
                                                    in
                                                 let maybe_range_arg =
                                                   let uu____15442 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____15442
                                                   then
                                                     let uu____15455 =
                                                       let uu____15464 =
                                                         FStar_TypeChecker_Cfg.embed_simple
                                                           FStar_Syntax_Embeddings.e_range
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                          in
                                                       FStar_Syntax_Syntax.as_arg
                                                         uu____15464
                                                        in
                                                     let uu____15465 =
                                                       let uu____15476 =
                                                         let uu____15485 =
                                                           FStar_TypeChecker_Cfg.embed_simple
                                                             FStar_Syntax_Embeddings.e_range
                                                             body2.FStar_Syntax_Syntax.pos
                                                             body2.FStar_Syntax_Syntax.pos
                                                            in
                                                         FStar_Syntax_Syntax.as_arg
                                                           uu____15485
                                                          in
                                                       [uu____15476]  in
                                                     uu____15455 ::
                                                       uu____15465
                                                   else []  in
                                                 let reified =
                                                   let args =
                                                     let uu____15534 =
                                                       FStar_Syntax_Util.is_layered
                                                         ed
                                                        in
                                                     if uu____15534
                                                     then
                                                       let unit_args =
                                                         let uu____15558 =
                                                           let uu____15559 =
                                                             let uu____15562
                                                               =
                                                               let uu____15563
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15563
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15562
                                                               FStar_Syntax_Subst.compress
                                                              in
                                                           uu____15559.FStar_Syntax_Syntax.n
                                                            in
                                                         match uu____15558
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_arrow
                                                             (uu____15604::uu____15605::bs,uu____15607)
                                                             when
                                                             (FStar_List.length
                                                                bs)
                                                               >=
                                                               (Prims.of_int (2))
                                                             ->
                                                             let uu____15659
                                                               =
                                                               let uu____15668
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   bs
                                                                   (FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2))))
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15668
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15659
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____15799
                                                                     ->
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.unit_const))
                                                         | uu____15806 ->
                                                             let uu____15807
                                                               =
                                                               let uu____15813
                                                                 =
                                                                 let uu____15815
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    ed.FStar_Syntax_Syntax.mname
                                                                    in
                                                                 let uu____15817
                                                                   =
                                                                   let uu____15819
                                                                    =
                                                                    let uu____15820
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    ed
                                                                    FStar_Syntax_Util.get_bind_vc_combinator
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15820
                                                                    FStar_Pervasives_Native.snd
                                                                     in
                                                                   FStar_All.pipe_right
                                                                    uu____15819
                                                                    FStar_Syntax_Print.term_to_string
                                                                    in
                                                                 FStar_Util.format2
                                                                   "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                                   uu____15815
                                                                   uu____15817
                                                                  in
                                                               (FStar_Errors.Fatal_UnexpectedEffect,
                                                                 uu____15813)
                                                                in
                                                             FStar_Errors.raise_error
                                                               uu____15807
                                                               rng
                                                          in
                                                       let uu____15854 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let uu____15863 =
                                                         let uu____15874 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t
                                                            in
                                                         let uu____15883 =
                                                           let uu____15894 =
                                                             let uu____15905
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head2
                                                                in
                                                             let uu____15914
                                                               =
                                                               let uu____15925
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   body2
                                                                  in
                                                               [uu____15925]
                                                                in
                                                             uu____15905 ::
                                                               uu____15914
                                                              in
                                                           FStar_List.append
                                                             unit_args
                                                             uu____15894
                                                            in
                                                         uu____15874 ::
                                                           uu____15883
                                                          in
                                                       uu____15854 ::
                                                         uu____15863
                                                     else
                                                       (let uu____15984 =
                                                          let uu____15995 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              lb.FStar_Syntax_Syntax.lbtyp
                                                             in
                                                          let uu____16004 =
                                                            let uu____16015 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t
                                                               in
                                                            [uu____16015]  in
                                                          uu____15995 ::
                                                            uu____16004
                                                           in
                                                        let uu____16048 =
                                                          let uu____16059 =
                                                            let uu____16070 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            let uu____16079 =
                                                              let uu____16090
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  head2
                                                                 in
                                                              let uu____16099
                                                                =
                                                                let uu____16110
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.tun
                                                                   in
                                                                let uu____16119
                                                                  =
                                                                  let uu____16130
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    body2  in
                                                                  [uu____16130]
                                                                   in
                                                                uu____16110
                                                                  ::
                                                                  uu____16119
                                                                 in
                                                              uu____16090 ::
                                                                uu____16099
                                                               in
                                                            uu____16070 ::
                                                              uu____16079
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____16059
                                                           in
                                                        FStar_List.append
                                                          uu____15984
                                                          uu____16048)
                                                      in
                                                   let uu____16195 =
                                                     let uu____16202 =
                                                       let uu____16203 =
                                                         let uu____16217 =
                                                           let uu____16220 =
                                                             let uu____16227
                                                               =
                                                               let uu____16228
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   head_bv
                                                                  in
                                                               [uu____16228]
                                                                in
                                                             FStar_Syntax_Subst.close
                                                               uu____16227
                                                              in
                                                           let uu____16247 =
                                                             FStar_Syntax_Syntax.mk
                                                               (FStar_Syntax_Syntax.Tm_app
                                                                  (bind_inst,
                                                                    args))
                                                               FStar_Pervasives_Native.None
                                                               rng
                                                              in
                                                           FStar_All.pipe_left
                                                             uu____16220
                                                             uu____16247
                                                            in
                                                         ((false, [lb_head]),
                                                           uu____16217)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_let
                                                         uu____16203
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____16202
                                                      in
                                                   uu____16195
                                                     FStar_Pervasives_Native.None
                                                     rng
                                                    in
                                                 (FStar_TypeChecker_Cfg.log
                                                    cfg
                                                    (fun uu____16279  ->
                                                       let uu____16280 =
                                                         FStar_Syntax_Print.term_to_string
                                                           top0
                                                          in
                                                       let uu____16282 =
                                                         FStar_Syntax_Print.term_to_string
                                                           reified
                                                          in
                                                       FStar_Util.print2
                                                         "Reified (1) <%s> to %s\n"
                                                         uu____16280
                                                         uu____16282);
                                                  (let uu____16285 =
                                                     FStar_List.tl stack  in
                                                   norm cfg env uu____16285
                                                     reified)))))))
                  | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                      ((let uu____16313 = FStar_Options.defensive ()  in
                        if uu____16313
                        then
                          let is_arg_impure uu____16328 =
                            match uu____16328 with
                            | (e,q) ->
                                let uu____16342 =
                                  let uu____16343 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16343.FStar_Syntax_Syntax.n  in
                                (match uu____16342 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____16359 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____16359
                                 | uu____16361 -> false)
                             in
                          let uu____16363 =
                            let uu____16365 =
                              let uu____16376 =
                                FStar_Syntax_Syntax.as_arg head1  in
                              uu____16376 :: args  in
                            FStar_Util.for_some is_arg_impure uu____16365  in
                          (if uu____16363
                           then
                             let uu____16402 =
                               let uu____16408 =
                                 let uu____16410 =
                                   FStar_Syntax_Print.term_to_string top2  in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____16410
                                  in
                               (FStar_Errors.Warning_Defensive, uu____16408)
                                in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu____16402
                           else ())
                        else ());
                       (let fallback1 uu____16423 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16427  ->
                               let uu____16428 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____16428 "");
                          (let uu____16432 = FStar_List.tl stack  in
                           let uu____16433 = FStar_Syntax_Util.mk_reify top2
                              in
                           norm cfg env uu____16432 uu____16433)
                           in
                        let fallback2 uu____16439 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16443  ->
                               let uu____16444 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____16444 "");
                          (let uu____16448 = FStar_List.tl stack  in
                           let uu____16449 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____16448 uu____16449)
                           in
                        let uu____16454 =
                          let uu____16455 = FStar_Syntax_Util.un_uinst head1
                             in
                          uu____16455.FStar_Syntax_Syntax.n  in
                        match uu____16454 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____16461 =
                              let uu____16463 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____16463  in
                            if uu____16461
                            then fallback1 ()
                            else
                              (let uu____16468 =
                                 let uu____16470 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____16470  in
                               if uu____16468
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____16487 =
                                      let uu____16492 =
                                        FStar_Syntax_Util.mk_reify head1  in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____16492 args
                                       in
                                    uu____16487 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____16493 = FStar_List.tl stack  in
                                  norm cfg env uu____16493 t1))
                        | uu____16494 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____16496) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____16520 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____16520  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____16524  ->
                            let uu____16525 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____16525);
                       (let uu____16528 = FStar_List.tl stack  in
                        norm cfg env uu____16528 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____16649  ->
                                match uu____16649 with
                                | (pat,wopt,tm) ->
                                    let uu____16697 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16697)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          top2.FStar_Syntax_Syntax.pos
                         in
                      let uu____16729 = FStar_List.tl stack  in
                      norm cfg env uu____16729 tm
                  | uu____16730 -> fallback ()))

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
              (fun uu____16744  ->
                 let uu____16745 = FStar_Ident.string_of_lid msrc  in
                 let uu____16747 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16749 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16745
                   uu____16747 uu____16749);
            (let uu____16752 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16755 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env)
                     in
                  Prims.op_Negation uu____16755)
                in
             if uu____16752
             then
               let ed =
                 let uu____16760 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16760  in
               let uu____16761 =
                 let uu____16770 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 FStar_All.pipe_right uu____16770 FStar_Util.must  in
               match uu____16761 with
               | (uu____16817,repr) ->
                   let uu____16827 =
                     let uu____16836 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr
                        in
                     FStar_All.pipe_right uu____16836 FStar_Util.must  in
                   (match uu____16827 with
                    | (uu____16883,return_repr) ->
                        let return_inst =
                          let uu____16896 =
                            let uu____16897 =
                              FStar_Syntax_Subst.compress return_repr  in
                            uu____16897.FStar_Syntax_Syntax.n  in
                          match uu____16896 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm,uu____16903::[]) ->
                              let uu____16908 =
                                let uu____16915 =
                                  let uu____16916 =
                                    let uu____16923 =
                                      let uu____16924 =
                                        env.FStar_TypeChecker_Env.universe_of
                                          env t
                                         in
                                      [uu____16924]  in
                                    (return_tm, uu____16923)  in
                                  FStar_Syntax_Syntax.Tm_uinst uu____16916
                                   in
                                FStar_Syntax_Syntax.mk uu____16915  in
                              uu____16908 FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                          | uu____16927 ->
                              failwith "NIY : Reification of indexed effects"
                           in
                        let uu____16931 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t
                             in
                          let lb =
                            let uu____16942 =
                              let uu____16945 =
                                let uu____16956 =
                                  FStar_Syntax_Syntax.as_arg t  in
                                [uu____16956]  in
                              FStar_Syntax_Util.mk_app repr uu____16945  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Util.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu____16942;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            }  in
                          let uu____16983 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (lb, bv, uu____16983)  in
                        (match uu____16931 with
                         | (lb_e,e_bv,e1) ->
                             let uu____16995 =
                               let uu____17002 =
                                 let uu____17003 =
                                   let uu____17017 =
                                     let uu____17020 =
                                       let uu____17027 =
                                         let uu____17028 =
                                           FStar_Syntax_Syntax.mk_binder e_bv
                                            in
                                         [uu____17028]  in
                                       FStar_Syntax_Subst.close uu____17027
                                        in
                                     let uu____17047 =
                                       let uu____17048 =
                                         let uu____17055 =
                                           let uu____17056 =
                                             let uu____17073 =
                                               let uu____17084 =
                                                 FStar_Syntax_Syntax.as_arg t
                                                  in
                                               let uu____17093 =
                                                 let uu____17104 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     e1
                                                    in
                                                 [uu____17104]  in
                                               uu____17084 :: uu____17093  in
                                             (return_inst, uu____17073)  in
                                           FStar_Syntax_Syntax.Tm_app
                                             uu____17056
                                            in
                                         FStar_Syntax_Syntax.mk uu____17055
                                          in
                                       uu____17048
                                         FStar_Pervasives_Native.None
                                         e1.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_All.pipe_left uu____17020
                                       uu____17047
                                      in
                                   ((false, [lb_e]), uu____17017)  in
                                 FStar_Syntax_Syntax.Tm_let uu____17003  in
                               FStar_Syntax_Syntax.mk uu____17002  in
                             uu____16995 FStar_Pervasives_Native.None
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu____17166 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17166 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17169 =
                      let uu____17171 = FStar_Ident.text_of_lid msrc  in
                      let uu____17173 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17171 uu____17173
                       in
                    failwith uu____17169
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17176;
                      FStar_TypeChecker_Env.mtarget = uu____17177;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17178;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17198 =
                      let uu____17200 = FStar_Ident.text_of_lid msrc  in
                      let uu____17202 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17200 uu____17202
                       in
                    failwith uu____17198
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17205;
                      FStar_TypeChecker_Env.mtarget = uu____17206;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17207;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____17238 =
                        FStar_TypeChecker_Env.is_reifiable_effect env msrc
                         in
                      if uu____17238
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____17243 =
                           let uu____17250 =
                             let uu____17251 =
                               let uu____17270 =
                                 let uu____17279 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____17279]  in
                               (uu____17270, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____17251  in
                           FStar_Syntax_Syntax.mk uu____17250  in
                         uu____17243 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____17312 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    lift uu____17312 t e1))

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
                (fun uu____17382  ->
                   match uu____17382 with
                   | (a,imp) ->
                       let uu____17401 = norm cfg env [] a  in
                       (uu____17401, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17411  ->
             let uu____17412 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17414 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17412 uu____17414);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17440 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17443  -> FStar_Pervasives_Native.Some _17443)
                     uu____17440
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2111_17444 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2111_17444.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2111_17444.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17466 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17469  -> FStar_Pervasives_Native.Some _17469)
                     uu____17466
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2122_17470 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2122_17470.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2122_17470.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17515  ->
                      match uu____17515 with
                      | (a,i) ->
                          let uu____17535 = norm cfg env [] a  in
                          (uu____17535, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17557  ->
                       match uu___14_17557 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17561 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17561
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2139_17569 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2141_17572 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2141_17572.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2139_17569.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2139_17569.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____17576 = b  in
        match uu____17576 with
        | (x,imp) ->
            let x1 =
              let uu___2149_17584 = x  in
              let uu____17585 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2149_17584.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2149_17584.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17585
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____17596 =
                    let uu____17597 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____17597  in
                  FStar_Pervasives_Native.Some uu____17596
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17608 =
          FStar_List.fold_left
            (fun uu____17642  ->
               fun b  ->
                 match uu____17642 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17608 with | (nbs,uu____17722) -> FStar_List.rev nbs

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
            let uu____17754 =
              let uu___2174_17755 = rc  in
              let uu____17756 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2174_17755.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17756;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2174_17755.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17754
        | uu____17774 -> lopt

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
            (let uu____17784 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17786 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17784 uu____17786)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_17798  ->
      match uu___15_17798 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17811 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17811 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17815 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____17815)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____17823 = norm_cb cfg  in
            reduce_primops uu____17823 cfg env tm  in
          let uu____17828 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17828
          then tm1
          else
            (let w t =
               let uu___2203_17847 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2203_17847.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2203_17847.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17859 =
                 let uu____17860 = FStar_Syntax_Util.unmeta t  in
                 uu____17860.FStar_Syntax_Syntax.n  in
               match uu____17859 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17872 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17936)::args1,(bv,uu____17939)::bs1) ->
                   let uu____17993 =
                     let uu____17994 = FStar_Syntax_Subst.compress t  in
                     uu____17994.FStar_Syntax_Syntax.n  in
                   (match uu____17993 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17999 -> false)
               | ([],[]) -> true
               | (uu____18030,uu____18031) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18082 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18084 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18082
                    uu____18084)
               else ();
               (let uu____18089 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18089 with
                | (hd1,args) ->
                    let uu____18128 =
                      let uu____18129 = FStar_Syntax_Subst.compress hd1  in
                      uu____18129.FStar_Syntax_Syntax.n  in
                    (match uu____18128 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____18137 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18139 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18141 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18137 uu____18139 uu____18141)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18146 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18164 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18166 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18164
                    uu____18166)
               else ();
               (let uu____18171 = FStar_Syntax_Util.is_squash t  in
                match uu____18171 with
                | FStar_Pervasives_Native.Some (uu____18182,t') ->
                    is_applied bs t'
                | uu____18194 ->
                    let uu____18203 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18203 with
                     | FStar_Pervasives_Native.Some (uu____18214,t') ->
                         is_applied bs t'
                     | uu____18226 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18250 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18250 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18257)::(q,uu____18259)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18302 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18304 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18302 uu____18304)
                    else ();
                    (let uu____18309 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18309 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18314 =
                           let uu____18315 = FStar_Syntax_Subst.compress p
                              in
                           uu____18315.FStar_Syntax_Syntax.n  in
                         (match uu____18314 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18326 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18326))
                          | uu____18329 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18332)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18357 =
                           let uu____18358 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18358.FStar_Syntax_Syntax.n  in
                         (match uu____18357 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18369 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18369))
                          | uu____18372 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18376 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18376 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18381 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18381 with
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
                                     let uu____18395 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18395))
                               | uu____18398 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18403)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18428 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18428 with
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
                                     let uu____18442 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18442))
                               | uu____18445 -> FStar_Pervasives_Native.None)
                          | uu____18448 -> FStar_Pervasives_Native.None)
                     | uu____18451 -> FStar_Pervasives_Native.None))
               | uu____18454 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18467 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18467 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18473)::[],uu____18474,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18494 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18496 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18494
                         uu____18496)
                    else ();
                    is_quantified_const bv phi')
               | uu____18501 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18516 =
                 let uu____18517 = FStar_Syntax_Subst.compress phi  in
                 uu____18517.FStar_Syntax_Syntax.n  in
               match uu____18516 with
               | FStar_Syntax_Syntax.Tm_match (uu____18523,br::brs) ->
                   let uu____18590 = br  in
                   (match uu____18590 with
                    | (uu____18608,uu____18609,e) ->
                        let r =
                          let uu____18631 = simp_t e  in
                          match uu____18631 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18643 =
                                FStar_List.for_all
                                  (fun uu____18662  ->
                                     match uu____18662 with
                                     | (uu____18676,uu____18677,e') ->
                                         let uu____18691 = simp_t e'  in
                                         uu____18691 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18643
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18707 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18717 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18717
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18755 =
                 match uu____18755 with
                 | (t1,q) ->
                     let uu____18776 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18776 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18808 -> (t1, q))
                  in
               let uu____18821 = FStar_Syntax_Util.head_and_args t  in
               match uu____18821 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18901 =
                 let uu____18902 = FStar_Syntax_Util.unmeta ty  in
                 uu____18902.FStar_Syntax_Syntax.n  in
               match uu____18901 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18907) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18912,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18936 -> false  in
             let simplify1 arg =
               let uu____18969 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18969, arg)  in
             let uu____18984 = is_forall_const tm1  in
             match uu____18984 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____18990 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18992 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18990
                       uu____18992)
                  else ();
                  (let uu____18997 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18997))
             | FStar_Pervasives_Native.None  ->
                 let uu____18998 =
                   let uu____18999 = FStar_Syntax_Subst.compress tm1  in
                   uu____18999.FStar_Syntax_Syntax.n  in
                 (match uu____18998 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19003;
                              FStar_Syntax_Syntax.vars = uu____19004;_},uu____19005);
                         FStar_Syntax_Syntax.pos = uu____19006;
                         FStar_Syntax_Syntax.vars = uu____19007;_},args)
                      ->
                      let uu____19037 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19037
                      then
                        let uu____19040 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19040 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19098)::
                             (uu____19099,(arg,uu____19101))::[] ->
                             maybe_auto_squash arg
                         | (uu____19174,(arg,uu____19176))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19177)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19250)::uu____19251::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19321::(FStar_Pervasives_Native.Some (false
                                         ),uu____19322)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19392 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19410 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19410
                         then
                           let uu____19413 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19413 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19471)::uu____19472::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19542::(FStar_Pervasives_Native.Some (true
                                           ),uu____19543)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19613)::(uu____19614,(arg,uu____19616))::[]
                               -> maybe_auto_squash arg
                           | (uu____19689,(arg,uu____19691))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19692)::[]
                               -> maybe_auto_squash arg
                           | uu____19765 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19783 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19783
                            then
                              let uu____19786 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19786 with
                              | uu____19844::(FStar_Pervasives_Native.Some
                                              (true ),uu____19845)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19915)::uu____19916::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19986)::(uu____19987,(arg,uu____19989))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20062,(p,uu____20064))::(uu____20065,
                                                                (q,uu____20067))::[]
                                  ->
                                  let uu____20139 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20139
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20144 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20162 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20162
                               then
                                 let uu____20165 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20165 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20223)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20224)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20298)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20299)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20373)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20374)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20448)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20449)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20523,(arg,uu____20525))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20526)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20599)::(uu____20600,(arg,uu____20602))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20675,(arg,uu____20677))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20678)::[]
                                     ->
                                     let uu____20751 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20751
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20752)::(uu____20753,(arg,uu____20755))::[]
                                     ->
                                     let uu____20828 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20828
                                 | (uu____20829,(p,uu____20831))::(uu____20832,
                                                                   (q,uu____20834))::[]
                                     ->
                                     let uu____20906 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20906
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20911 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20929 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20929
                                  then
                                    let uu____20932 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20932 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20990)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21034)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21078 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21096 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21096
                                     then
                                       match args with
                                       | (t,uu____21100)::[] ->
                                           let uu____21125 =
                                             let uu____21126 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21126.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21125 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21129::[],body,uu____21131)
                                                ->
                                                let uu____21166 = simp_t body
                                                   in
                                                (match uu____21166 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21172 -> tm1)
                                            | uu____21176 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21178))::(t,uu____21180)::[]
                                           ->
                                           let uu____21220 =
                                             let uu____21221 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21221.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21220 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21224::[],body,uu____21226)
                                                ->
                                                let uu____21261 = simp_t body
                                                   in
                                                (match uu____21261 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21269 -> tm1)
                                            | uu____21273 -> tm1)
                                       | uu____21274 -> tm1
                                     else
                                       (let uu____21287 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21287
                                        then
                                          match args with
                                          | (t,uu____21291)::[] ->
                                              let uu____21316 =
                                                let uu____21317 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21317.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21316 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21320::[],body,uu____21322)
                                                   ->
                                                   let uu____21357 =
                                                     simp_t body  in
                                                   (match uu____21357 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21363 -> tm1)
                                               | uu____21367 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21369))::(t,uu____21371)::[]
                                              ->
                                              let uu____21411 =
                                                let uu____21412 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21412.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21411 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21415::[],body,uu____21417)
                                                   ->
                                                   let uu____21452 =
                                                     simp_t body  in
                                                   (match uu____21452 with
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
                                                    | uu____21460 -> tm1)
                                               | uu____21464 -> tm1)
                                          | uu____21465 -> tm1
                                        else
                                          (let uu____21478 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21478
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21481;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21482;_},uu____21483)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21509;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21510;_},uu____21511)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21537 -> tm1
                                           else
                                             (let uu____21550 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____21550
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____21564 =
                                                    let uu____21565 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____21565.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____21564 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21576 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21590 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____21590
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____21629 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____21629
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21635 =
                                                         let uu____21636 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____21636.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____21635 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21639 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____21647 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____21647
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21656
                                                                  =
                                                                  let uu____21657
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____21657.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____21656
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____21663)
                                                                    -> hd1
                                                                | uu____21688
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____21692
                                                                =
                                                                let uu____21703
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____21703]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21692)
                                                       | uu____21736 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21741 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____21741 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21761 ->
                                                     let uu____21770 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____21770 cfg env
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21776;
                         FStar_Syntax_Syntax.vars = uu____21777;_},args)
                      ->
                      let uu____21803 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21803
                      then
                        let uu____21806 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21806 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21864)::
                             (uu____21865,(arg,uu____21867))::[] ->
                             maybe_auto_squash arg
                         | (uu____21940,(arg,uu____21942))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21943)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22016)::uu____22017::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22087::(FStar_Pervasives_Native.Some (false
                                         ),uu____22088)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22158 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22176 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22176
                         then
                           let uu____22179 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22179 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22237)::uu____22238::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22308::(FStar_Pervasives_Native.Some (true
                                           ),uu____22309)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22379)::(uu____22380,(arg,uu____22382))::[]
                               -> maybe_auto_squash arg
                           | (uu____22455,(arg,uu____22457))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22458)::[]
                               -> maybe_auto_squash arg
                           | uu____22531 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22549 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22549
                            then
                              let uu____22552 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____22552 with
                              | uu____22610::(FStar_Pervasives_Native.Some
                                              (true ),uu____22611)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22681)::uu____22682::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22752)::(uu____22753,(arg,uu____22755))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22828,(p,uu____22830))::(uu____22831,
                                                                (q,uu____22833))::[]
                                  ->
                                  let uu____22905 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22905
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22910 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22928 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22928
                               then
                                 let uu____22931 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____22931 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22989)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22990)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23064)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23065)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23139)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23140)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23214)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23215)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23289,(arg,uu____23291))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23292)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23365)::(uu____23366,(arg,uu____23368))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23441,(arg,uu____23443))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23444)::[]
                                     ->
                                     let uu____23517 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23517
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23518)::(uu____23519,(arg,uu____23521))::[]
                                     ->
                                     let uu____23594 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23594
                                 | (uu____23595,(p,uu____23597))::(uu____23598,
                                                                   (q,uu____23600))::[]
                                     ->
                                     let uu____23672 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23672
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23677 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23695 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23695
                                  then
                                    let uu____23698 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23698 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23756)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23800)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23844 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23862 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23862
                                     then
                                       match args with
                                       | (t,uu____23866)::[] ->
                                           let uu____23891 =
                                             let uu____23892 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23892.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23891 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23895::[],body,uu____23897)
                                                ->
                                                let uu____23932 = simp_t body
                                                   in
                                                (match uu____23932 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23938 -> tm1)
                                            | uu____23942 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23944))::(t,uu____23946)::[]
                                           ->
                                           let uu____23986 =
                                             let uu____23987 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23987.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23986 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23990::[],body,uu____23992)
                                                ->
                                                let uu____24027 = simp_t body
                                                   in
                                                (match uu____24027 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24035 -> tm1)
                                            | uu____24039 -> tm1)
                                       | uu____24040 -> tm1
                                     else
                                       (let uu____24053 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24053
                                        then
                                          match args with
                                          | (t,uu____24057)::[] ->
                                              let uu____24082 =
                                                let uu____24083 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24083.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24082 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24086::[],body,uu____24088)
                                                   ->
                                                   let uu____24123 =
                                                     simp_t body  in
                                                   (match uu____24123 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24129 -> tm1)
                                               | uu____24133 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24135))::(t,uu____24137)::[]
                                              ->
                                              let uu____24177 =
                                                let uu____24178 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24178.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24177 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24181::[],body,uu____24183)
                                                   ->
                                                   let uu____24218 =
                                                     simp_t body  in
                                                   (match uu____24218 with
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
                                                    | uu____24226 -> tm1)
                                               | uu____24230 -> tm1)
                                          | uu____24231 -> tm1
                                        else
                                          (let uu____24244 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24244
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24247;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24248;_},uu____24249)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24275;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24276;_},uu____24277)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24303 -> tm1
                                           else
                                             (let uu____24316 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____24316
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____24330 =
                                                    let uu____24331 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____24331.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____24330 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____24342 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24356 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____24356
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____24391 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____24391
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24397 =
                                                         let uu____24398 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____24398.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____24397 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24401 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24409 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24409
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24418
                                                                  =
                                                                  let uu____24419
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24419.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24418
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____24425)
                                                                    -> hd1
                                                                | uu____24450
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____24454
                                                                =
                                                                let uu____24465
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____24465]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24454)
                                                       | uu____24498 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24503 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____24503 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24523 ->
                                                     let uu____24532 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____24532 cfg env
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24543 = simp_t t  in
                      (match uu____24543 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24552 ->
                      let uu____24575 = is_const_match tm1  in
                      (match uu____24575 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24584 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____24594  ->
               (let uu____24596 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24598 = FStar_Syntax_Print.term_to_string t  in
                let uu____24600 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24608 =
                  let uu____24610 =
                    let uu____24613 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24613
                     in
                  stack_to_string uu____24610  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24596 uu____24598 uu____24600 uu____24608);
               (let uu____24638 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24638
                then
                  let uu____24642 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24642 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24649 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24651 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24653 =
                          let uu____24655 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24655
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24649
                          uu____24651 uu____24653);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____24677 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____24685)::uu____24686 -> true
                | uu____24696 -> false)
              in
           if uu____24677
           then
             let uu____24699 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____24699 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____24713 =
                        let uu____24715 =
                          let uu____24717 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____24717  in
                        FStar_Util.string_of_int uu____24715  in
                      let uu____24724 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____24726 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                      let uu____24728 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____24713 uu____24724 uu____24726 uu____24728)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____24737,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24766  ->
                        let uu____24767 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24767);
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
                  let uu____24810 =
                    let uu___2832_24811 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2832_24811.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2832_24811.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____24810
              | (Arg (Univ uu____24814,uu____24815,uu____24816))::uu____24817
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____24821,uu____24822))::uu____24823 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____24839,uu____24840),aq,r))::stack1
                  when
                  let uu____24892 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24892 ->
                  let t2 =
                    let uu____24896 =
                      let uu____24901 =
                        let uu____24902 = closure_as_term cfg env_arg tm  in
                        (uu____24902, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____24901  in
                    uu____24896 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____24912),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24967  ->
                        let uu____24968 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____24968);
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
                     (let uu____24988 = FStar_ST.op_Bang m  in
                      match uu____24988 with
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
                      | FStar_Pervasives_Native.Some (uu____25076,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____25132 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____25137  ->
                         let uu____25138 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____25138);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____25148 =
                    let uu____25149 = FStar_Syntax_Subst.compress t1  in
                    uu____25149.FStar_Syntax_Syntax.n  in
                  (match uu____25148 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____25177 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____25177  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____25181  ->
                             let uu____25182 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____25182);
                        (let uu____25185 = FStar_List.tl stack  in
                         norm cfg env1 uu____25185 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____25186);
                          FStar_Syntax_Syntax.pos = uu____25187;
                          FStar_Syntax_Syntax.vars = uu____25188;_},(e,uu____25190)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____25229 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____25246 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____25246 with
                        | (hd1,args) ->
                            let uu____25289 =
                              let uu____25290 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____25290.FStar_Syntax_Syntax.n  in
                            (match uu____25289 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____25294 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____25294 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____25297;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____25298;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____25299;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____25301;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____25302;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____25303;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____25304;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____25340 -> fallback " (3)" ())
                             | uu____25344 -> fallback " (4)" ()))
                   | uu____25346 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (CBVApp (env',head1,aq,r))::stack1 ->
                  let uu____25369 =
                    let uu____25370 =
                      let uu____25371 =
                        let uu____25378 =
                          let uu____25379 =
                            let uu____25411 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env, t1, uu____25411, false)  in
                          Clos uu____25379  in
                        (uu____25378, aq, (t1.FStar_Syntax_Syntax.pos))  in
                      Arg uu____25371  in
                    uu____25370 :: stack1  in
                  norm cfg env' uu____25369 head1
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____25486  ->
                        let uu____25487 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____25487);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____25498 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25503  ->
                           let uu____25504 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____25506 =
                             let uu____25508 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____25538  ->
                                       match uu____25538 with
                                       | (p,uu____25549,uu____25550) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____25508
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____25504 uu____25506);
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
                                   (fun uu___16_25575  ->
                                      match uu___16_25575 with
                                      | FStar_TypeChecker_Env.InliningDelta 
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                           -> true
                                      | uu____25579 -> false))
                               in
                            let steps =
                              let uu___3009_25582 =
                                cfg1.FStar_TypeChecker_Cfg.steps  in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3009_25582.FStar_TypeChecker_Cfg.for_extraction)
                              }  in
                            let uu___3012_25589 = cfg1  in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3012_25589.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3012_25589.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3012_25589.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3012_25589.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3012_25589.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3012_25589.FStar_TypeChecker_Cfg.reifying)
                            })
                          in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____25664 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____25695 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25784  ->
                                       fun uu____25785  ->
                                         match (uu____25784, uu____25785)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____25935 =
                                               norm_pat env3 p1  in
                                             (match uu____25935 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____25695 with
                              | (pats1,env3) ->
                                  ((let uu___3040_26105 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3040_26105.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3044_26126 = x  in
                               let uu____26127 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3044_26126.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3044_26126.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26127
                               }  in
                             ((let uu___3047_26141 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3047_26141.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3051_26152 = x  in
                               let uu____26153 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3051_26152.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3051_26152.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26153
                               }  in
                             ((let uu___3054_26167 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3054_26167.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3060_26183 = x  in
                               let uu____26184 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3060_26183.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3060_26183.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26184
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3064_26199 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3064_26199.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____26243 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____26273 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____26273 with
                                     | (p,wopt,e) ->
                                         let uu____26293 = norm_pat env1 p
                                            in
                                         (match uu____26293 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____26348 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____26348
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____26365 =
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
                         if uu____26365
                         then
                           norm
                             (let uu___3083_26372 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3085_26375 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.zeta_full =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.zeta_full);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3085_26375.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3083_26372.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3083_26372.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3083_26372.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3083_26372.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3083_26372.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3083_26372.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3083_26372.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3083_26372.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____26379 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____26379)
                       in
                    let rec is_cons head1 =
                      let uu____26405 =
                        let uu____26406 = FStar_Syntax_Subst.compress head1
                           in
                        uu____26406.FStar_Syntax_Syntax.n  in
                      match uu____26405 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____26411) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____26416 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26418;
                            FStar_Syntax_Syntax.fv_delta = uu____26419;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26421;
                            FStar_Syntax_Syntax.fv_delta = uu____26422;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____26423);_}
                          -> true
                      | uu____26431 -> false  in
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
                      let uu____26600 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____26600 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____26697 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26739 ->
                                    let uu____26740 =
                                      let uu____26742 = is_cons head1  in
                                      Prims.op_Negation uu____26742  in
                                    FStar_Util.Inr uu____26740)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____26771 =
                                 let uu____26772 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____26772.FStar_Syntax_Syntax.n  in
                               (match uu____26771 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26791 ->
                                    let uu____26792 =
                                      let uu____26794 = is_cons head1  in
                                      Prims.op_Negation uu____26794  in
                                    FStar_Util.Inr uu____26792))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____26885)::rest_a,(p1,uu____26888)::rest_p)
                          ->
                          let uu____26947 = matches_pat t2 p1  in
                          (match uu____26947 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____27000 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____27123 = matches_pat scrutinee1 p1  in
                          (match uu____27123 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____27169  ->
                                     let uu____27170 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____27172 =
                                       let uu____27174 =
                                         FStar_List.map
                                           (fun uu____27186  ->
                                              match uu____27186 with
                                              | (uu____27192,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____27174
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____27170 uu____27172);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____27228  ->
                                          match uu____27228 with
                                          | (bv,t2) ->
                                              let uu____27251 =
                                                let uu____27258 =
                                                  let uu____27261 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____27261
                                                   in
                                                let uu____27262 =
                                                  let uu____27263 =
                                                    let uu____27295 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____27295,
                                                      false)
                                                     in
                                                  Clos uu____27263  in
                                                (uu____27258, uu____27262)
                                                 in
                                              uu____27251 :: env2) env1 s
                                    in
                                 let uu____27388 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____27388)))
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
            (fun uu____27421  ->
               let uu____27422 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____27422);
          (let uu____27425 = is_nbe_request s  in
           if uu____27425
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27431  ->
                   let uu____27432 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27432);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27438  ->
                   let uu____27439 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27439);
              (let uu____27442 =
                 FStar_Util.record_time (fun uu____27449  -> nbe_eval c s t)
                  in
               match uu____27442 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27458  ->
                         let uu____27459 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27461 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27459 uu____27461);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27469  ->
                   let uu____27470 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27470);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27476  ->
                   let uu____27477 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27477);
              (let uu____27480 =
                 FStar_Util.record_time (fun uu____27487  -> norm c [] [] t)
                  in
               match uu____27480 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27502  ->
                         let uu____27503 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27505 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27503 uu____27505);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27524 =
          let uu____27528 =
            let uu____27530 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____27530  in
          FStar_Pervasives_Native.Some uu____27528  in
        FStar_Profiling.profile
          (fun uu____27533  -> normalize_with_primitive_steps [] s e t)
          uu____27524 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____27555  ->
             let uu____27556 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27556);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27562  ->
             let uu____27563 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27563);
        (let uu____27566 =
           FStar_Util.record_time (fun uu____27573  -> norm_comp cfg [] c)
            in
         match uu____27566 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27588  ->
                   let uu____27589 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____27591 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27589
                     uu____27591);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27605 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____27605 [] u
  
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
      let uu____27627 = normalize steps env t  in
      FStar_TypeChecker_Env.non_informative env uu____27627
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27639 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env t ->
          let uu___3253_27658 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3253_27658.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3253_27658.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27665 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27665
          then
            let ct1 =
              let uu____27669 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27669 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____27676 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27676
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3263_27683 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3263_27683.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3263_27683.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3263_27683.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c
                     in
                  let uu___3267_27685 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3267_27685.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3267_27685.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3267_27685.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3267_27685.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3270_27686 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3270_27686.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3270_27686.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27689 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      let uu____27701 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____27701
      then
        let uu____27704 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____27704 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3278_27708 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3278_27708.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3278_27708.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3278_27708.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3285_27727  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3284_27730 ->
            ((let uu____27732 =
                let uu____27738 =
                  let uu____27740 = FStar_Util.message_of_exn uu___3284_27730
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27740
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27738)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27732);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3295_27759  ->
             match () with
             | () ->
                 let uu____27760 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____27760 [] c) ()
        with
        | uu___3294_27769 ->
            ((let uu____27771 =
                let uu____27777 =
                  let uu____27779 = FStar_Util.message_of_exn uu___3294_27769
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27779
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27777)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27771);
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
                   let uu____27828 =
                     let uu____27829 =
                       let uu____27836 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27836)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27829  in
                   mk uu____27828 t01.FStar_Syntax_Syntax.pos
               | uu____27841 -> t2)
          | uu____27842 -> t2  in
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
        let uu____27936 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27936 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27949 ->
                 let uu____27950 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27950 with
                  | (actuals,uu____27960,uu____27961) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27981 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27981 with
                         | (binders,args) ->
                             let uu____27992 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27992
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
      | uu____28007 ->
          let uu____28008 = FStar_Syntax_Util.head_and_args t  in
          (match uu____28008 with
           | (head1,args) ->
               let uu____28051 =
                 let uu____28052 = FStar_Syntax_Subst.compress head1  in
                 uu____28052.FStar_Syntax_Syntax.n  in
               (match uu____28051 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____28073 =
                      let uu____28080 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____28080  in
                    (match uu____28073 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____28104 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3365_28112 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3365_28112.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3365_28112.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3365_28112.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3365_28112.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3365_28112.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3365_28112.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3365_28112.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3365_28112.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3365_28112.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3365_28112.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3365_28112.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3365_28112.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3365_28112.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3365_28112.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3365_28112.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3365_28112.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3365_28112.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3365_28112.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3365_28112.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3365_28112.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3365_28112.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3365_28112.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3365_28112.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3365_28112.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3365_28112.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3365_28112.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3365_28112.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3365_28112.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3365_28112.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3365_28112.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3365_28112.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3365_28112.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3365_28112.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3365_28112.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3365_28112.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3365_28112.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3365_28112.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3365_28112.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3365_28112.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3365_28112.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3365_28112.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3365_28112.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3365_28112.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3365_28112.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____28104 with
                            | (uu____28115,ty,uu____28117) ->
                                eta_expand_with_type env t ty))
                | uu____28118 ->
                    let uu____28119 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3372_28127 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3372_28127.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3372_28127.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3372_28127.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3372_28127.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3372_28127.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3372_28127.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3372_28127.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3372_28127.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3372_28127.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3372_28127.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3372_28127.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3372_28127.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3372_28127.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3372_28127.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3372_28127.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3372_28127.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3372_28127.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3372_28127.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3372_28127.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3372_28127.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3372_28127.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3372_28127.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3372_28127.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3372_28127.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3372_28127.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3372_28127.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3372_28127.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3372_28127.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3372_28127.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3372_28127.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3372_28127.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3372_28127.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3372_28127.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3372_28127.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3372_28127.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3372_28127.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3372_28127.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3372_28127.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3372_28127.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3372_28127.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3372_28127.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3372_28127.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3372_28127.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3372_28127.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____28119 with
                     | (uu____28130,ty,uu____28132) ->
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
      let uu___3384_28214 = x  in
      let uu____28215 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3384_28214.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3384_28214.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28215
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28218 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28234 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28235 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28236 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28237 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28244 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28245 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28246 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3410_28280 = rc  in
          let uu____28281 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28290 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3410_28280.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28281;
            FStar_Syntax_Syntax.residual_flags = uu____28290
          }  in
        let uu____28293 =
          let uu____28294 =
            let uu____28313 = elim_delayed_subst_binders bs  in
            let uu____28322 = elim_delayed_subst_term t2  in
            let uu____28325 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28313, uu____28322, uu____28325)  in
          FStar_Syntax_Syntax.Tm_abs uu____28294  in
        mk1 uu____28293
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28362 =
          let uu____28363 =
            let uu____28378 = elim_delayed_subst_binders bs  in
            let uu____28387 = elim_delayed_subst_comp c  in
            (uu____28378, uu____28387)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28363  in
        mk1 uu____28362
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28406 =
          let uu____28407 =
            let uu____28414 = elim_bv bv  in
            let uu____28415 = elim_delayed_subst_term phi  in
            (uu____28414, uu____28415)  in
          FStar_Syntax_Syntax.Tm_refine uu____28407  in
        mk1 uu____28406
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28446 =
          let uu____28447 =
            let uu____28464 = elim_delayed_subst_term t2  in
            let uu____28467 = elim_delayed_subst_args args  in
            (uu____28464, uu____28467)  in
          FStar_Syntax_Syntax.Tm_app uu____28447  in
        mk1 uu____28446
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3432_28539 = p  in
              let uu____28540 =
                let uu____28541 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28541  in
              {
                FStar_Syntax_Syntax.v = uu____28540;
                FStar_Syntax_Syntax.p =
                  (uu___3432_28539.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3436_28543 = p  in
              let uu____28544 =
                let uu____28545 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28545  in
              {
                FStar_Syntax_Syntax.v = uu____28544;
                FStar_Syntax_Syntax.p =
                  (uu___3436_28543.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3442_28552 = p  in
              let uu____28553 =
                let uu____28554 =
                  let uu____28561 = elim_bv x  in
                  let uu____28562 = elim_delayed_subst_term t0  in
                  (uu____28561, uu____28562)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28554  in
              {
                FStar_Syntax_Syntax.v = uu____28553;
                FStar_Syntax_Syntax.p =
                  (uu___3442_28552.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3448_28587 = p  in
              let uu____28588 =
                let uu____28589 =
                  let uu____28603 =
                    FStar_List.map
                      (fun uu____28629  ->
                         match uu____28629 with
                         | (x,b) ->
                             let uu____28646 = elim_pat x  in
                             (uu____28646, b)) pats
                     in
                  (fv, uu____28603)  in
                FStar_Syntax_Syntax.Pat_cons uu____28589  in
              {
                FStar_Syntax_Syntax.v = uu____28588;
                FStar_Syntax_Syntax.p =
                  (uu___3448_28587.FStar_Syntax_Syntax.p)
              }
          | uu____28661 -> p  in
        let elim_branch uu____28685 =
          match uu____28685 with
          | (pat,wopt,t3) ->
              let uu____28711 = elim_pat pat  in
              let uu____28714 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28717 = elim_delayed_subst_term t3  in
              (uu____28711, uu____28714, uu____28717)
           in
        let uu____28722 =
          let uu____28723 =
            let uu____28746 = elim_delayed_subst_term t2  in
            let uu____28749 = FStar_List.map elim_branch branches  in
            (uu____28746, uu____28749)  in
          FStar_Syntax_Syntax.Tm_match uu____28723  in
        mk1 uu____28722
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28880 =
          match uu____28880 with
          | (tc,topt) ->
              let uu____28915 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28925 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28925
                | FStar_Util.Inr c ->
                    let uu____28927 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28927
                 in
              let uu____28928 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28915, uu____28928)
           in
        let uu____28937 =
          let uu____28938 =
            let uu____28965 = elim_delayed_subst_term t2  in
            let uu____28968 = elim_ascription a  in
            (uu____28965, uu____28968, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28938  in
        mk1 uu____28937
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3478_29031 = lb  in
          let uu____29032 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____29035 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3478_29031.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3478_29031.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____29032;
            FStar_Syntax_Syntax.lbeff =
              (uu___3478_29031.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____29035;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3478_29031.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3478_29031.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____29038 =
          let uu____29039 =
            let uu____29053 =
              let uu____29061 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____29061)  in
            let uu____29073 = elim_delayed_subst_term t2  in
            (uu____29053, uu____29073)  in
          FStar_Syntax_Syntax.Tm_let uu____29039  in
        mk1 uu____29038
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____29118 =
          let uu____29119 =
            let uu____29126 = elim_delayed_subst_term tm  in
            (uu____29126, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____29119  in
        mk1 uu____29118
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29137 =
          let uu____29138 =
            let uu____29145 = elim_delayed_subst_term t2  in
            let uu____29148 = elim_delayed_subst_meta md  in
            (uu____29145, uu____29148)  in
          FStar_Syntax_Syntax.Tm_meta uu____29138  in
        mk1 uu____29137

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29157  ->
         match uu___17_29157 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29161 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29161
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
        let uu____29184 =
          let uu____29185 =
            let uu____29194 = elim_delayed_subst_term t  in
            (uu____29194, uopt)  in
          FStar_Syntax_Syntax.Total uu____29185  in
        mk1 uu____29184
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29211 =
          let uu____29212 =
            let uu____29221 = elim_delayed_subst_term t  in
            (uu____29221, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29212  in
        mk1 uu____29211
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3511_29230 = ct  in
          let uu____29231 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29234 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29245 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3511_29230.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3511_29230.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29231;
            FStar_Syntax_Syntax.effect_args = uu____29234;
            FStar_Syntax_Syntax.flags = uu____29245
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29248  ->
    match uu___18_29248 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____29283 =
          let uu____29304 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____29313 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29304, uu____29313)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29283
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____29368 =
          let uu____29375 = elim_delayed_subst_term t  in (m, uu____29375)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____29368
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____29387 =
          let uu____29396 = elim_delayed_subst_term t  in
          (m1, m2, uu____29396)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29387
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
      (fun uu____29429  ->
         match uu____29429 with
         | (t,q) ->
             let uu____29448 = elim_delayed_subst_term t  in (uu____29448, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29476  ->
         match uu____29476 with
         | (x,q) ->
             let uu____29495 =
               let uu___3537_29496 = x  in
               let uu____29497 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3537_29496.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3537_29496.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29497
               }  in
             (uu____29495, q)) bs

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
            | (uu____29605,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29637,FStar_Util.Inl t) ->
                let uu____29659 =
                  let uu____29666 =
                    let uu____29667 =
                      let uu____29682 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29682)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29667  in
                  FStar_Syntax_Syntax.mk uu____29666  in
                uu____29659 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29695 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29695 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29727 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29800 ->
                    let uu____29801 =
                      let uu____29810 =
                        let uu____29811 = FStar_Syntax_Subst.compress t4  in
                        uu____29811.FStar_Syntax_Syntax.n  in
                      (uu____29810, tc)  in
                    (match uu____29801 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29840) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29887) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29932,FStar_Util.Inl uu____29933) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29964 -> failwith "Impossible")
                 in
              (match uu____29727 with
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
          let uu____30103 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____30103 with
          | (univ_names1,binders1,tc) ->
              let uu____30177 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30177)
  
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
          let uu____30231 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____30231 with
          | (univ_names1,binders1,tc) ->
              let uu____30305 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30305)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____30347 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____30347 with
           | (univ_names1,binders1,typ1) ->
               let uu___3620_30387 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3620_30387.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3620_30387.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3620_30387.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3620_30387.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3620_30387.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3626_30402 = s  in
          let uu____30403 =
            let uu____30404 =
              let uu____30413 = FStar_List.map (elim_uvars env) sigs  in
              (uu____30413, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____30404  in
          {
            FStar_Syntax_Syntax.sigel = uu____30403;
            FStar_Syntax_Syntax.sigrng =
              (uu___3626_30402.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3626_30402.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3626_30402.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3626_30402.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3626_30402.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____30432 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30432 with
           | (univ_names1,uu____30456,typ1) ->
               let uu___3640_30478 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3640_30478.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3640_30478.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3640_30478.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3640_30478.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3640_30478.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____30485 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30485 with
           | (univ_names1,uu____30509,typ1) ->
               let uu___3651_30531 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3651_30531.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3651_30531.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3651_30531.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3651_30531.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3651_30531.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30561 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30561 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____30586 =
                            let uu____30587 =
                              let uu____30588 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____30588  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30587
                             in
                          elim_delayed_subst_term uu____30586  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3667_30591 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3667_30591.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3667_30591.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3667_30591.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3667_30591.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3670_30592 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3670_30592.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3670_30592.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3670_30592.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3670_30592.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3670_30592.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3674_30599 = s  in
          let uu____30600 =
            let uu____30601 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____30601  in
          {
            FStar_Syntax_Syntax.sigel = uu____30600;
            FStar_Syntax_Syntax.sigrng =
              (uu___3674_30599.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3674_30599.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3674_30599.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3674_30599.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3674_30599.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____30605 = elim_uvars_aux_t env us [] t  in
          (match uu____30605 with
           | (us1,uu____30629,t1) ->
               let uu___3685_30651 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3685_30651.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3685_30651.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3685_30651.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3685_30651.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3685_30651.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30653 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____30653 with
           | (univs1,binders,uu____30672) ->
               let uu____30693 =
                 let uu____30698 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____30698 with
                 | (univs_opening,univs2) ->
                     let uu____30721 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____30721)
                  in
               (match uu____30693 with
                | (univs_opening,univs_closing) ->
                    let uu____30724 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30730 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30731 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30730, uu____30731)  in
                    (match uu____30724 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30757 =
                           match uu____30757 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30775 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30775 with
                                | (us1,t1) ->
                                    let uu____30786 =
                                      let uu____30795 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30800 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30795, uu____30800)  in
                                    (match uu____30786 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30823 =
                                           let uu____30832 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____30837 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____30832, uu____30837)  in
                                         (match uu____30823 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30861 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30861
                                                 in
                                              let uu____30862 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30862 with
                                               | (uu____30889,uu____30890,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30913 =
                                                       let uu____30914 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30914
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30913
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30923 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____30923 with
                           | (uu____30942,uu____30943,t1) -> t1  in
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
                             | uu____31019 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____31046 =
                               let uu____31047 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____31047.FStar_Syntax_Syntax.n  in
                             match uu____31046 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____31106 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31140 =
                               let uu____31141 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31141.FStar_Syntax_Syntax.n  in
                             match uu____31140 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31164) ->
                                 let uu____31189 = destruct_action_body body
                                    in
                                 (match uu____31189 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31238 ->
                                 let uu____31239 = destruct_action_body t  in
                                 (match uu____31239 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31294 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31294 with
                           | (action_univs,t) ->
                               let uu____31303 = destruct_action_typ_templ t
                                  in
                               (match uu____31303 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3769_31350 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3769_31350.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3769_31350.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3772_31352 = ed  in
                           let uu____31353 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____31354 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____31355 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3772_31352.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3772_31352.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31353;
                             FStar_Syntax_Syntax.combinators = uu____31354;
                             FStar_Syntax_Syntax.actions = uu____31355;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3772_31352.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3775_31358 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3775_31358.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3775_31358.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3775_31358.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3775_31358.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3775_31358.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31379 =
            match uu___19_31379 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____31410 = elim_uvars_aux_t env us [] t  in
                (match uu____31410 with
                 | (us1,uu____31442,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3790_31473 = sub_eff  in
            let uu____31474 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____31477 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3790_31473.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3790_31473.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31474;
              FStar_Syntax_Syntax.lift = uu____31477
            }  in
          let uu___3793_31480 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3793_31480.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3793_31480.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3793_31480.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3793_31480.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3793_31480.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____31490 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____31490 with
           | (univ_names1,binders1,comp1) ->
               let uu___3806_31530 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3806_31530.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3806_31530.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3806_31530.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3806_31530.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3806_31530.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31533 -> s
      | FStar_Syntax_Syntax.Sig_fail uu____31534 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31547 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n1,p,(us_t,t),(us_ty,ty))
          ->
          let uu____31577 = elim_uvars_aux_t env us_t [] t  in
          (match uu____31577 with
           | (us_t1,uu____31601,t1) ->
               let uu____31623 = elim_uvars_aux_t env us_ty [] ty  in
               (match uu____31623 with
                | (us_ty1,uu____31647,ty1) ->
                    let uu___3833_31669 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n1, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3833_31669.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3833_31669.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3833_31669.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3833_31669.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3833_31669.FStar_Syntax_Syntax.sigopts)
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
        let uu____31720 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____31720 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____31742 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____31742 with
             | (uu____31749,head_def) ->
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
      let uu____31755 = FStar_Syntax_Util.head_and_args t  in
      match uu____31755 with
      | (head1,args) ->
          let uu____31800 =
            let uu____31801 = FStar_Syntax_Subst.compress head1  in
            uu____31801.FStar_Syntax_Syntax.n  in
          (match uu____31800 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31808;
                  FStar_Syntax_Syntax.vars = uu____31809;_},us)
               -> aux fv us args
           | uu____31815 -> FStar_Pervasives_Native.None)
  