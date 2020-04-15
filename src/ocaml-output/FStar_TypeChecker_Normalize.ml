open Prims
let cases :
  'uuuuuu10 'uuuuuu11 .
    ('uuuuuu10 -> 'uuuuuu11) ->
      'uuuuuu11 -> 'uuuuuu10 FStar_Pervasives_Native.option -> 'uuuuuu11
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
    match uu____982 with | (hd,uu____998) -> hd
  
let mk :
  'uuuuuu1026 .
    'uuuuuu1026 ->
      FStar_Range.range -> 'uuuuuu1026 FStar_Syntax_Syntax.syntax
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
    | Clos (env1,t,uu____1132,uu____1133) ->
        let uu____1180 =
          FStar_All.pipe_right (FStar_List.length env1)
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
  fun env1  ->
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
               FStar_Util.format2 "(%s, %s)" uu____1249 uu____1254) env1
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
  
let is_empty : 'uuuuuu1383 . 'uuuuuu1383 Prims.list -> Prims.bool =
  fun uu___3_1391  ->
    match uu___3_1391 with | [] -> true | uu____1395 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env1  ->
    fun x  ->
      try
        (fun uu___121_1428  ->
           match () with
           | () ->
               let uu____1429 =
                 FStar_List.nth env1 x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1429) ()
      with
      | uu___120_1446 ->
          let uu____1447 =
            let uu____1449 = FStar_Syntax_Print.db_to_string x  in
            let uu____1451 = env_to_string env1  in
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
    fun env1  ->
      fun u  ->
        let norm_univs_for_max us =
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
                        | (k_u,n) ->
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
                 (fun uu___155_1632  ->
                    match () with
                    | () ->
                        let uu____1635 =
                          let uu____1636 = FStar_List.nth env1 x  in
                          FStar_Pervasives_Native.snd uu____1636  in
                        (match uu____1635 with
                         | Univ u3 ->
                             ((let uu____1655 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____1655
                               then
                                 let uu____1660 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1660
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____1665 ->
                             let uu____1666 =
                               let uu____1668 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1668
                                in
                             failwith uu____1666)) ()
               with
               | uu____1678 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1684 =
                        let uu____1686 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____1686
                         in
                      failwith uu____1684))
          | FStar_Syntax_Syntax.U_unif uu____1691 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1700 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1709 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1716 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1716 norm_univs_for_max  in
              (match us1 with
               | u_k::hd::rest ->
                   let rest1 = hd :: rest  in
                   let uu____1733 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1733 with
                    | (FStar_Syntax_Syntax.U_zero ,n) ->
                        let uu____1744 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1754 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1754 with
                                  | (uu____1761,m) -> n <= m))
                           in
                        if uu____1744 then rest1 else us1
                    | uu____1770 -> us1)
               | uu____1776 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1780 = aux u3  in
              FStar_List.map
                (fun uu____1783  -> FStar_Syntax_Syntax.U_succ uu____1783)
                uu____1780
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1787 = aux u  in
           match uu____1787 with
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
    fun env1  ->
      fun stack1  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____1948  ->
               let uu____1949 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1951 = env_to_string env1  in
               let uu____1953 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 ">>> %s (env=%s)\nClosure_as_term %s\n"
                 uu____1949 uu____1951 uu____1953);
          (match env1 with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env1 stack1 t
           | uu____1966 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1969 ->
                    let uu____1984 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env1 stack1 uu____1984
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_constant uu____1985 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_name uu____1986 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_lazy uu____1987 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_fvar uu____1988 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____2013 ->
                           let uu____2026 =
                             let uu____2028 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____2030 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____2028 uu____2030
                              in
                           failwith uu____2026
                       | uu____2035 -> inline_closure_env cfg env1 stack1 t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_2071  ->
                                         match uu___4_2071 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____2078 =
                                               let uu____2085 =
                                                 inline_closure_env cfg env1
                                                   [] t1
                                                  in
                                               (x, uu____2085)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____2078
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___249_2097 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___249_2097.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___249_2097.FStar_Syntax_Syntax.sort)
                                                  })
                                                in
                                             let t1 =
                                               inline_closure_env cfg env1 []
                                                 x_i
                                                in
                                             (match t1.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_bvar
                                                  x_j ->
                                                  FStar_Syntax_Syntax.NM
                                                    (x,
                                                      (x_j.FStar_Syntax_Syntax.index))
                                              | uu____2103 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____2106 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___258_2111 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___258_2111.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___258_2111.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____2132 =
                        let uu____2133 = norm_universe cfg env1 u  in
                        FStar_Syntax_Syntax.Tm_type uu____2133  in
                      mk uu____2132 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____2141 =
                        FStar_List.map (norm_universe cfg env1) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2141  in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____2143 = lookup_bvar env1 x  in
                    (match uu____2143 with
                     | Univ uu____2146 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___274_2151 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___274_2151.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___274_2151.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env1 stack1 t1
                     | Clos (env2,t0,uu____2157,uu____2158) ->
                         inline_closure_env cfg env2 stack1 t0)
                | FStar_Syntax_Syntax.Tm_app (head,args) ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____2249  ->
                              fun stack2  ->
                                match uu____2249 with
                                | (a,aq) ->
                                    let uu____2261 =
                                      let uu____2262 =
                                        let uu____2269 =
                                          let uu____2270 =
                                            let uu____2302 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env1, a, uu____2302, false)  in
                                          Clos uu____2270  in
                                        (uu____2269, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2262  in
                                    uu____2261 :: stack2) args)
                       in
                    inline_closure_env cfg env1 stack2 head
                | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                    let env' =
                      FStar_All.pipe_right env1
                        (FStar_List.fold_right
                           (fun _b  ->
                              fun env2  ->
                                (FStar_Pervasives_Native.None, Dummy) :: env2)
                           bs)
                       in
                    let stack2 =
                      (Abs
                         (env1, bs, env', lopt, (t.FStar_Syntax_Syntax.pos)))
                      :: stack1  in
                    inline_closure_env cfg env' stack2 body
                | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                    let uu____2470 = close_binders cfg env1 bs  in
                    (match uu____2470 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____2520) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env1 stack1
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2531 =
                      let uu____2544 =
                        let uu____2553 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2553]  in
                      close_binders cfg env1 uu____2544  in
                    (match uu____2531 with
                     | (x1,env2) ->
                         let phi1 = non_tail_inline_closure_env cfg env2 phi
                            in
                         let t1 =
                           let uu____2598 =
                             let uu____2599 =
                               let uu____2606 =
                                 let uu____2607 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2607
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2606, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2599  in
                           mk uu____2598 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env2 stack1 t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2706 =
                            non_tail_inline_closure_env cfg env1 t2  in
                          FStar_Util.Inl uu____2706
                      | FStar_Util.Inr c ->
                          let uu____2720 = close_comp cfg env1 c  in
                          FStar_Util.Inr uu____2720
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env1)
                       in
                    let t2 =
                      let uu____2739 =
                        let uu____2740 =
                          let uu____2767 =
                            non_tail_inline_closure_env cfg env1 t1  in
                          (uu____2767, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2740  in
                      mk uu____2739 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env1 stack1 t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2813 =
                            let uu____2814 =
                              let uu____2821 =
                                non_tail_inline_closure_env cfg env1 t'  in
                              (uu____2821, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2814  in
                          mk uu____2813 t.FStar_Syntax_Syntax.pos
                      | FStar_Syntax_Syntax.Quote_static  ->
                          let qi1 =
                            FStar_Syntax_Syntax.on_antiquoted
                              (non_tail_inline_closure_env cfg env1) qi
                             in
                          mk (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
                            t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_meta (t',m) ->
                    let stack2 =
                      (Meta (env1, m, (t.FStar_Syntax_Syntax.pos))) :: stack1
                       in
                    inline_closure_env cfg env1 stack2 t'
                | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                    let env0 = env1  in
                    let env2 =
                      FStar_List.fold_left
                        (fun env2  -> fun uu____2876  -> dummy :: env2) env1
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    let typ =
                      non_tail_inline_closure_env cfg env2
                        lb.FStar_Syntax_Syntax.lbtyp
                       in
                    let def =
                      non_tail_inline_closure_env cfg env2
                        lb.FStar_Syntax_Syntax.lbdef
                       in
                    let uu____2897 =
                      let uu____2908 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2908
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2930 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___366_2946 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___366_2946.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___366_2946.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2930))
                       in
                    (match uu____2897 with
                     | (nm,body1) ->
                         let attrs =
                           FStar_List.map
                             (non_tail_inline_closure_env cfg env0)
                             lb.FStar_Syntax_Syntax.lbattrs
                            in
                         let lb1 =
                           let uu___372_2973 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___372_2973.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___372_2973.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs = attrs;
                             FStar_Syntax_Syntax.lbpos =
                               (uu___372_2973.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack1 t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2990,lbs),body) ->
                    let norm_one_lb env2 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____3056  -> fun env3  -> dummy :: env3)
                          lb.FStar_Syntax_Syntax.lbunivs env2
                         in
                      let env3 =
                        let uu____3073 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____3073
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____3088  -> fun env3  -> dummy :: env3)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____3112 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____3112
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___395_3123 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___395_3123.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___395_3123.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___398_3124 = lb  in
                      let uu____3125 =
                        non_tail_inline_closure_env cfg env3
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___398_3124.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___398_3124.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____3125;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___398_3124.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___398_3124.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env1))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____3157  -> fun env2  -> dummy :: env2)
                          lbs1 env1
                         in
                      non_tail_inline_closure_env cfg body_env body  in
                    let t1 =
                      mk (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
                        t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_match (head,branches1) ->
                    let stack2 =
                      (Match
                         (env1, branches1, cfg, (t.FStar_Syntax_Syntax.pos)))
                      :: stack1  in
                    inline_closure_env cfg env1 stack2 head))

and (non_tail_inline_closure_env :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun cfg  -> fun env1  -> fun t  -> inline_closure_env cfg env1 [] t

and (rebuild_closure :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____3249  ->
               let uu____3250 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3252 = env_to_string env1  in
               let uu____3254 = stack_to_string stack1  in
               let uu____3256 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 ">>> %s (env=%s, stack=%s)\nRebuild closure_as_term %s\n"
                 uu____3250 uu____3252 uu____3254 uu____3256);
          (match stack1 with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3263,uu____3264),aq,r))::stack2 ->
               let stack3 = (App (env1, t, aq, r)) :: stack2  in
               inline_closure_env cfg env_arg stack3 tm
           | (App (env2,head,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env2 stack2 t1
           | (CBVApp (env2,head,aq,r))::stack2 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env2 stack2 t1
           | (Abs (env',bs,env'',lopt,r))::stack2 ->
               let uu____3359 = close_binders cfg env' bs  in
               (match uu____3359 with
                | (bs1,uu____3375) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3395 =
                      let uu___465_3398 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___465_3398.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___465_3398.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env1 stack2 uu____3395)
           | (Match (env2,branches1,cfg1,r))::stack2 ->
               let close_one_branch env3 uu____3454 =
                 match uu____3454 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env4 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3569 ->
                           (p, env4)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3600 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3689  ->
                                     fun uu____3690  ->
                                       match (uu____3689, uu____3690) with
                                       | ((pats1,env5),(p1,b)) ->
                                           let uu____3840 = norm_pat env5 p1
                                              in
                                           (match uu____3840 with
                                            | (p2,env6) ->
                                                (((p2, b) :: pats1), env6)))
                                  ([], env4))
                              in
                           (match uu____3600 with
                            | (pats1,env5) ->
                                ((let uu___502_4010 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___502_4010.FStar_Syntax_Syntax.p)
                                  }), env5))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___506_4031 = x  in
                             let uu____4032 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___506_4031.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___506_4031.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4032
                             }  in
                           ((let uu___509_4046 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___509_4046.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___513_4057 = x  in
                             let uu____4058 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___513_4057.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___513_4057.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4058
                             }  in
                           ((let uu___516_4072 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___516_4072.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___522_4088 = x  in
                             let uu____4089 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___522_4088.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___522_4088.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4089
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env4 t1
                              in
                           ((let uu___526_4106 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___526_4106.FStar_Syntax_Syntax.p)
                             }), env4)
                        in
                     let uu____4111 = norm_pat env3 pat  in
                     (match uu____4111 with
                      | (pat1,env4) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____4180 =
                                  non_tail_inline_closure_env cfg1 env4 w  in
                                FStar_Pervasives_Native.Some uu____4180
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env4 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____4199 =
                   let uu____4200 =
                     let uu____4223 =
                       FStar_All.pipe_right branches1
                         (FStar_List.map (close_one_branch env2))
                        in
                     (t, uu____4223)  in
                   FStar_Syntax_Syntax.Tm_match uu____4200  in
                 mk uu____4199 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env2 stack2 t1
           | (Meta (env_m,m,r))::stack2 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names,args) ->
                     let uu____4359 =
                       let uu____4380 =
                         FStar_All.pipe_right names
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m))
                          in
                       let uu____4397 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1  ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4506  ->
                                         match uu____4506 with
                                         | (a,q) ->
                                             let uu____4533 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a
                                                in
                                             (uu____4533, q)))))
                          in
                       (uu____4380, uu____4397)  in
                     FStar_Syntax_Syntax.Meta_pattern uu____4359
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4562 =
                       let uu____4569 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4569)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4562
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4581 =
                       let uu____4590 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4590)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4581
                 | uu____4595 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env1 stack2 t1
           | uu____4601 -> failwith "Impossible: unexpected stack element")

and (close_imp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env1  ->
      fun imp  ->
        match imp with
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
            let uu____4617 =
              let uu____4618 = inline_closure_env cfg env1 [] t  in
              FStar_Syntax_Syntax.Meta uu____4618  in
            FStar_Pervasives_Native.Some uu____4617
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
    fun env1  ->
      fun bs  ->
        let uu____4635 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4719  ->
                  fun uu____4720  ->
                    match (uu____4719, uu____4720) with
                    | ((env2,out),(b,imp)) ->
                        let b1 =
                          let uu___581_4860 = b  in
                          let uu____4861 =
                            inline_closure_env cfg env2 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___581_4860.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___581_4860.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4861
                          }  in
                        let imp1 = close_imp cfg env2 imp  in
                        let env3 = dummy :: env2  in
                        (env3, ((b1, imp1) :: out))) (env1, []))
           in
        match uu____4635 with | (env2,bs1) -> ((FStar_List.rev bs1), env2)

and (close_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun cfg  ->
    fun env1  ->
      fun c  ->
        match env1 with
        | [] when
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
            -> c
        | uu____5003 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5016 = inline_closure_env cfg env1 [] t  in
                 let uu____5017 =
                   FStar_Option.map (norm_universe cfg env1) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5016 uu____5017
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5030 = inline_closure_env cfg env1 [] t  in
                 let uu____5031 =
                   FStar_Option.map (norm_universe cfg env1) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5030 uu____5031
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env1 []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5085  ->
                           match uu____5085 with
                           | (a,q) ->
                               let uu____5106 =
                                 inline_closure_env cfg env1 [] a  in
                               (uu____5106, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_5123  ->
                           match uu___5_5123 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5127 =
                                 inline_closure_env cfg env1 [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5127
                           | f -> f))
                    in
                 let uu____5131 =
                   let uu___614_5132 = c1  in
                   let uu____5133 =
                     FStar_List.map (norm_universe cfg env1)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5133;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___614_5132.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5131)

and (close_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env1  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              FStar_All.pipe_right rc.FStar_Syntax_Syntax.residual_flags
                (FStar_List.filter
                   (fun uu___6_5151  ->
                      match uu___6_5151 with
                      | FStar_Syntax_Syntax.DECREASES uu____5153 -> false
                      | uu____5157 -> true))
               in
            let rc1 =
              let uu___626_5160 = rc  in
              let uu____5161 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env1 [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___626_5160.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5161;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5170 -> lopt

let (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___7_5191  ->
            match uu___7_5191 with
            | FStar_Syntax_Syntax.DECREASES uu____5193 -> false
            | uu____5197 -> true))
  
let (closure_as_term :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun cfg  -> fun env1  -> fun t  -> non_tail_inline_closure_env cfg env1 t 
let (unembed_binder_knot :
  FStar_Syntax_Syntax.binder FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (unembed_binder :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____5244 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____5244 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5283 = FStar_Syntax_Embeddings.unembed e t  in
        uu____5283 false FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'uuuuuu5303 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'uuuuuu5303) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env1  ->
      FStar_List.fold_right
        (fun uu____5365  ->
           fun subst  ->
             match uu____5365 with
             | (binder_opt,closure1) ->
                 (match (binder_opt, closure1) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env2,term,uu____5406,uu____5407)) ->
                      let uu____5468 = b  in
                      (match uu____5468 with
                       | (bv,uu____5476) ->
                           let uu____5477 =
                             let uu____5479 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5479  in
                           if uu____5477
                           then subst
                           else
                             (let term1 = closure_as_term cfg env2 term  in
                              let uu____5487 = unembed_binder term1  in
                              match uu____5487 with
                              | FStar_Pervasives_Native.None  -> subst
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5494 =
                                      let uu___666_5495 = bv  in
                                      let uu____5496 =
                                        FStar_Syntax_Subst.subst subst
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___666_5495.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___666_5495.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5496
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5494
                                     in
                                  let b_for_x =
                                    let uu____5502 =
                                      let uu____5509 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5509)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5502  in
                                  let subst1 =
                                    FStar_List.filter
                                      (fun uu___8_5525  ->
                                         match uu___8_5525 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5527,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5529;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5530;_})
                                             ->
                                             let uu____5535 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5535
                                         | uu____5537 -> true) subst
                                     in
                                  b_for_x :: subst1))
                  | uu____5539 -> subst)) env1 []
  
let reduce_primops :
  'uuuuuu5561 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5561)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun env1  ->
        fun tm  ->
          if
            Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
          then tm
          else
            (let uu____5613 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5613 with
             | (head,args) ->
                 let uu____5658 =
                   let uu____5659 = FStar_Syntax_Util.un_uinst head  in
                   uu____5659.FStar_Syntax_Syntax.n  in
                 (match uu____5658 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5665 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5665 with
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
                                (fun uu____5688  ->
                                   let uu____5689 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5691 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5693 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5689 uu____5691 uu____5693);
                              tm)
                           else
                             (let uu____5698 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5698 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5784  ->
                                        let uu____5785 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5785);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5790  ->
                                             if
                                               prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                                             then mk_psc_subst cfg env1
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
                                           (fun uu____5804  ->
                                              let uu____5805 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5805);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5813  ->
                                              let uu____5814 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5816 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5814 uu____5816);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5819 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5823  ->
                                 let uu____5824 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5824);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5830  ->
                            let uu____5831 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5831);
                       (match args with
                        | (a1,uu____5837)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5862 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5876  ->
                            let uu____5877 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5877);
                       (match args with
                        | (t,uu____5883)::(r,uu____5885)::[] ->
                            let uu____5926 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5926 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5932 -> tm))
                  | uu____5943 -> tm))
  
let reduce_equality :
  'uuuuuu5954 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5954)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___754_6003 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___756_6006 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___756_6006.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___756_6006.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___756_6006.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.zeta_full =
                    (uu___756_6006.FStar_TypeChecker_Cfg.zeta_full);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___756_6006.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___756_6006.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___756_6006.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___756_6006.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___756_6006.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___756_6006.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___756_6006.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___756_6006.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___756_6006.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___756_6006.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___756_6006.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___756_6006.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___756_6006.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___756_6006.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___756_6006.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___756_6006.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___756_6006.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___756_6006.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___756_6006.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___756_6006.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___756_6006.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___756_6006.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___754_6003.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___754_6003.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___754_6003.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___754_6003.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___754_6003.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___754_6003.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___754_6003.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____6017 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____6028 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____6039 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd  ->
    fun args  ->
      let aux min_args =
        let uu____6060 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____6060
          (fun n  ->
             if n < min_args
             then Norm_request_none
             else
               if n = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____6092 =
        let uu____6093 = FStar_Syntax_Util.un_uinst hd  in
        uu____6093.FStar_Syntax_Syntax.n  in
      match uu____6092 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu____6102 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____6111 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____6111)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd  ->
    fun args  ->
      let uu____6124 =
        let uu____6125 = FStar_Syntax_Util.un_uinst hd  in
        uu____6125.FStar_Syntax_Syntax.n  in
      match uu____6124 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6183 = FStar_Syntax_Util.mk_app hd [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____6183 rest
           | uu____6210 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6250 = FStar_Syntax_Util.mk_app hd [t]  in
               FStar_Syntax_Util.mk_app uu____6250 rest
           | uu____6269 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____6343 = FStar_Syntax_Util.mk_app hd [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____6343 rest
           | uu____6378 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6380 ->
          let uu____6381 =
            let uu____6383 = FStar_Syntax_Print.term_to_string hd  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6383
             in
          failwith uu____6381
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6404  ->
    match uu___9_6404 with
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
    | FStar_Syntax_Embeddings.UnfoldOnly names ->
        let uu____6411 =
          let uu____6414 =
            let uu____6415 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6415  in
          [uu____6414]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6411
    | FStar_Syntax_Embeddings.UnfoldFully names ->
        let uu____6423 =
          let uu____6426 =
            let uu____6427 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldFully uu____6427  in
          [uu____6426]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6423
    | FStar_Syntax_Embeddings.UnfoldAttr names ->
        let uu____6435 =
          let uu____6438 =
            let uu____6439 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6439  in
          [uu____6438]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6435
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s  ->
    let s1 = FStar_List.concatMap tr_norm_step s  in
    let add_exclude s2 z =
      let uu____6475 =
        FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2  in
      if uu____6475 then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2  in
    let s2 = FStar_TypeChecker_Env.Beta :: s1  in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta  in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota  in s4
  
let get_norm_request :
  'uuuuuu6500 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu6500) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6551 =
            let uu____6556 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6556 s  in
          match uu____6551 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6572 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6572
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
        | uu____6607::(tm,uu____6609)::[] ->
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
        | (tm,uu____6638)::[] ->
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
        | (steps,uu____6659)::uu____6660::(tm,uu____6662)::[] ->
            let uu____6683 =
              let uu____6688 = full_norm steps  in parse_steps uu____6688  in
            (match uu____6683 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s), tm))
        | uu____6718 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6750 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6757  ->
                    match uu___10_6757 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6759 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6761 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6765 -> true
                    | uu____6769 -> false))
             in
          if uu____6750
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6779  ->
             let uu____6780 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6780);
        (let tm_norm =
           let uu____6784 =
             let uu____6799 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6799.FStar_TypeChecker_Env.nbe  in
           uu____6784 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6803  ->
              let uu____6804 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6804);
         tm_norm)
  
let firstn :
  'uuuuuu6814 .
    Prims.int ->
      'uuuuuu6814 Prims.list ->
        ('uuuuuu6814 Prims.list * 'uuuuuu6814 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack1  ->
      let rec drop_irrel uu___11_6871 =
        match uu___11_6871 with
        | (MemoLazy uu____6876)::s -> drop_irrel s
        | (UnivArgs uu____6886)::s -> drop_irrel s
        | s -> s  in
      let uu____6899 = drop_irrel stack1  in
      match uu____6899 with
      | (App
          (uu____6903,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6904;
                        FStar_Syntax_Syntax.vars = uu____6905;_},uu____6906,uu____6907))::uu____6908
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6913 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6942) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6952) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6973  ->
                  match uu____6973 with
                  | (a,uu____6984) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6995 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____7012 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____7014 -> false
    | FStar_Syntax_Syntax.Tm_type uu____7028 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____7030 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____7032 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____7034 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____7036 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____7039 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____7047 -> false
    | FStar_Syntax_Syntax.Tm_let uu____7055 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____7070 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____7090 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____7106 -> true
    | FStar_Syntax_Syntax.Tm_match uu____7114 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7186  ->
                   match uu____7186 with
                   | (a,uu____7197) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7208) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____7307,args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7362  ->
                        match uu____7362 with
                        | (a,uu____7373) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7382,uu____7383,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7389,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7395 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7405 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7407 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7418 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7429 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7440 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7451 -> false
  
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
            let uu____7484 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7484 with
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
              (fun uu____7683  ->
                 fun uu____7684  ->
                   match (uu____7683, uu____7684) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7790 =
            match uu____7790 with
            | (x,y,z) ->
                let uu____7810 = FStar_Util.string_of_bool x  in
                let uu____7812 = FStar_Util.string_of_bool y  in
                let uu____7814 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7810 uu____7812
                  uu____7814
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7842  ->
                    let uu____7843 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7845 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7843 uu____7845);
               if b then reif else no)
            else
              if
                (let uu____7860 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7860)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7865  ->
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
                          ((is_rec,uu____7900),uu____7901);
                        FStar_Syntax_Syntax.sigrng = uu____7902;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7904;
                        FStar_Syntax_Syntax.sigattrs = uu____7905;
                        FStar_Syntax_Syntax.sigopts = uu____7906;_},uu____7907),uu____7908),uu____7909,uu____7910,uu____7911)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8020  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____8022,uu____8023,uu____8024,uu____8025) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8092  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____8095),uu____8096);
                        FStar_Syntax_Syntax.sigrng = uu____8097;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____8099;
                        FStar_Syntax_Syntax.sigattrs = uu____8100;
                        FStar_Syntax_Syntax.sigopts = uu____8101;_},uu____8102),uu____8103),uu____8104,uu____8105,uu____8106)
                     when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8215  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8217,FStar_Pervasives_Native.Some
                    uu____8218,uu____8219,uu____8220) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8288  ->
                           let uu____8289 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8289);
                      (let uu____8292 =
                         let uu____8304 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8330 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8330
                            in
                         let uu____8342 =
                           let uu____8354 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8380 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8380
                              in
                           let uu____8396 =
                             let uu____8408 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8434 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8434
                                in
                             [uu____8408]  in
                           uu____8354 :: uu____8396  in
                         uu____8304 :: uu____8342  in
                       comb_or uu____8292))
                 | (uu____8482,uu____8483,FStar_Pervasives_Native.Some
                    uu____8484,uu____8485) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8553  ->
                           let uu____8554 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8554);
                      (let uu____8557 =
                         let uu____8569 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8595 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8595
                            in
                         let uu____8607 =
                           let uu____8619 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8645 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8645
                              in
                           let uu____8661 =
                             let uu____8673 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8699 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8699
                                in
                             [uu____8673]  in
                           uu____8619 :: uu____8661  in
                         uu____8569 :: uu____8607  in
                       comb_or uu____8557))
                 | (uu____8747,uu____8748,uu____8749,FStar_Pervasives_Native.Some
                    uu____8750) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8818  ->
                           let uu____8819 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8819);
                      (let uu____8822 =
                         let uu____8834 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8860 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8860
                            in
                         let uu____8872 =
                           let uu____8884 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8910 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8910
                              in
                           let uu____8926 =
                             let uu____8938 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8964 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8964
                                in
                             [uu____8938]  in
                           uu____8884 :: uu____8926  in
                         uu____8834 :: uu____8872  in
                       comb_or uu____8822))
                 | uu____9012 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____9058  ->
                           let uu____9059 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____9061 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____9063 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____9059 uu____9061 uu____9063);
                      (let uu____9066 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_9072  ->
                                 match uu___12_9072 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____9078 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____9078 l))
                          in
                       FStar_All.pipe_left yesno uu____9066)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____9094  ->
               let uu____9095 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____9097 =
                 let uu____9099 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____9099  in
               let uu____9100 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____9095 uu____9097 uu____9100);
          (match res with
           | (false ,uu____9103,uu____9104) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____9129 ->
               let uu____9139 =
                 let uu____9141 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9141
                  in
               FStar_All.pipe_left failwith uu____9139)
  
let decide_unfolding :
  'uuuuuu9160 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'uuuuuu9160 ->
            FStar_Syntax_Syntax.fv ->
              FStar_TypeChecker_Env.qninfo ->
                (FStar_TypeChecker_Cfg.cfg * stack_elt Prims.list)
                  FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun rng  ->
          fun fv  ->
            fun qninfo  ->
              let res =
                should_unfold cfg (fun cfg1  -> should_reify cfg1 stack1) fv
                  qninfo
                 in
              match res with
              | Should_unfold_no  -> FStar_Pervasives_Native.None
              | Should_unfold_yes  ->
                  FStar_Pervasives_Native.Some (cfg, stack1)
              | Should_unfold_fully  ->
                  let cfg' =
                    let uu___1165_9229 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1167_9232 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1167_9232.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1167_9232.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1165_9229.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1165_9229.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1165_9229.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1165_9229.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1165_9229.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1165_9229.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1165_9229.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1165_9229.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  let stack' =
                    match stack1 with
                    | (UnivArgs (us,r))::stack' -> (UnivArgs (us, r)) ::
                        (Cfg cfg) :: stack'
                    | stack' -> (Cfg cfg) :: stack'  in
                  FStar_Pervasives_Native.Some (cfg', stack')
              | Should_unfold_reify  ->
                  let rec push e s =
                    match s with
                    | [] -> [e]
                    | (UnivArgs (us,r))::t ->
                        let uu____9294 = push e t  in (UnivArgs (us, r)) ::
                          uu____9294
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9306 =
                      let uu____9313 =
                        let uu____9314 =
                          let uu____9315 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____9315  in
                        FStar_Syntax_Syntax.Tm_constant uu____9314  in
                      FStar_Syntax_Syntax.mk uu____9313  in
                    uu____9306 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let stack2 =
                    push
                      (App
                         (env1, ref, FStar_Pervasives_Native.None,
                           FStar_Range.dummyRange)) stack1
                     in
                  FStar_Pervasives_Native.Some (cfg, stack2)
  
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
    let uu____9381 =
      let uu____9382 = FStar_Syntax_Subst.compress t  in
      uu____9382.FStar_Syntax_Syntax.n  in
    match uu____9381 with
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____9413 =
          let uu____9414 = FStar_Syntax_Util.un_uinst hd  in
          uu____9414.FStar_Syntax_Syntax.n  in
        (match uu____9413 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9431 =
                 let uu____9438 =
                   let uu____9449 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9449 FStar_List.tl  in
                 FStar_All.pipe_right uu____9438 FStar_List.hd  in
               FStar_All.pipe_right uu____9431 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9548 -> FStar_Pervasives_Native.None)
    | uu____9549 -> FStar_Pervasives_Native.None
  
let rec (norm :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun t  ->
          let t1 =
            if
              (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.norm_delayed
            then
              (match t.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_delayed uu____9828 ->
                   let uu____9843 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9843
               | uu____9846 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9856  ->
               let uu____9857 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9859 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9861 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9863 =
                 FStar_Util.string_of_int (FStar_List.length env1)  in
               let uu____9871 =
                 let uu____9873 =
                   let uu____9876 = firstn (Prims.of_int (4)) stack1  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9876
                    in
                 stack_to_string uu____9873  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9857 uu____9859 uu____9861 uu____9863 uu____9871);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9904  ->
               let uu____9905 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9905);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9911  ->
                     let uu____9912 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9912);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9915 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9919  ->
                     let uu____9920 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9920);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____9923 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9927  ->
                     let uu____9928 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9928);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9931 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9935  ->
                     let uu____9936 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9936);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9939;
                 FStar_Syntax_Syntax.fv_delta = uu____9940;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9944  ->
                     let uu____9945 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9945);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9948;
                 FStar_Syntax_Syntax.fv_delta = uu____9949;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9950);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9960  ->
                     let uu____9961 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9961);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____9967 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____9967 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level uu____9970)
                    when uu____9970 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9974  ->
                          let uu____9975 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9975);
                     rebuild cfg env1 stack1 t1)
                | uu____9978 ->
                    let uu____9981 =
                      decide_unfolding cfg env1 stack1
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____9981 with
                     | FStar_Pervasives_Native.Some (cfg1,stack2) ->
                         do_unfold_fv cfg1 env1 stack2 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env1 stack1 t1))
           | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
               let qi1 =
                 FStar_Syntax_Syntax.on_antiquoted (norm cfg env1 []) qi  in
               let t2 =
                 mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                   t1.FStar_Syntax_Syntax.pos
                  in
               let uu____10020 = closure_as_term cfg env1 t2  in
               rebuild cfg env1 stack1 uu____10020
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10048 = is_norm_request hd args  in
                  uu____10048 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____10054 = rejig_norm_request hd args  in
                 norm cfg env1 stack1 uu____10054))
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10082 = is_norm_request hd args  in
                  uu____10082 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1278_10089 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1280_10092 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1280_10092.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1278_10089.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1278_10089.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1278_10089.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1278_10089.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1278_10089.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1278_10089.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____10099 =
                   get_norm_request cfg (norm cfg' env1 []) args  in
                 match uu____10099 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack2 =
                         FStar_All.pipe_right stack1
                           (FStar_List.fold_right
                              (fun uu____10135  ->
                                 fun stack2  ->
                                   match uu____10135 with
                                   | (a,aq) ->
                                       let uu____10147 =
                                         let uu____10148 =
                                           let uu____10155 =
                                             let uu____10156 =
                                               let uu____10188 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env1, a, uu____10188, false)
                                                in
                                             Clos uu____10156  in
                                           (uu____10155, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10148  in
                                       uu____10147 :: stack2) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10256  ->
                            let uu____10257 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10257);
                       norm cfg env1 stack2 hd))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     let tm' = closure_as_term cfg env1 tm  in
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
                         let uu____10289 =
                           let uu____10291 =
                             let uu____10293 = FStar_Util.time_diff start fin
                                in
                             FStar_Pervasives_Native.snd uu____10293  in
                           FStar_Util.string_of_int uu____10291  in
                         let uu____10300 =
                           FStar_Syntax_Print.term_to_string tm'  in
                         let uu____10302 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                         let uu____10304 =
                           FStar_Syntax_Print.term_to_string tm_norm  in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____10289 uu____10300 uu____10302 uu____10304)
                      else ();
                      rebuild cfg env1 stack1 tm_norm)
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     let delta_level =
                       let uu____10324 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___13_10331  ->
                                 match uu___13_10331 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____10333 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____10335 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____10339 -> true
                                 | uu____10343 -> false))
                          in
                       if uu____10324
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let cfg'1 =
                       let uu___1318_10351 = cfg  in
                       let uu____10352 =
                         let uu___1320_10353 =
                           FStar_TypeChecker_Cfg.to_fsteps s  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1320_10353.FStar_TypeChecker_Cfg.for_extraction)
                         }  in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____10352;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1318_10351.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1318_10351.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1318_10351.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1318_10351.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1318_10351.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___1318_10351.FStar_TypeChecker_Cfg.reifying)
                       }  in
                     let stack' =
                       let tail = (Cfg cfg) :: stack1  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____10361 =
                           let uu____10362 =
                             let uu____10367 = FStar_Util.now ()  in
                             (tm, uu____10367)  in
                           Debug uu____10362  in
                         uu____10361 :: tail
                       else tail  in
                     norm cfg'1 env1 stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env1 u  in
               let uu____10372 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env1 stack1 uu____10372
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env1 stack1 t'
               else
                 (let us1 =
                    let uu____10383 =
                      let uu____10390 =
                        FStar_List.map (norm_universe cfg env1) us  in
                      (uu____10390, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10383  in
                  let stack2 = us1 :: stack1  in norm cfg env1 stack2 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10399 = lookup_bvar env1 x  in
               (match uu____10399 with
                | Univ uu____10400 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env2,t0,r,fix) ->
                    if
                      ((Prims.op_Negation fix) ||
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                        ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full
                    then
                      let uu____10454 = FStar_ST.op_Bang r  in
                      (match uu____10454 with
                       | FStar_Pervasives_Native.Some (env3,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10550  ->
                                 let uu____10551 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10553 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10551
                                   uu____10553);
                            (let uu____10556 = maybe_weakly_reduced t'  in
                             if uu____10556
                             then
                               match stack1 with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env3 stack1 t'
                               | uu____10559 -> norm cfg env3 stack1 t'
                             else rebuild cfg env3 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env2 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env2 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____10603)::uu____10604 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10615,uu____10616))::stack_rest ->
                    (match c with
                     | Univ uu____10620 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env1)
                           stack_rest t1
                     | uu____10629 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10659  ->
                                    let uu____10660 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10660);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env1) stack_rest body)
                          | b::tl ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10696  ->
                                    let uu____10697 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10697);
                               (let body1 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_abs
                                       (tl, body, lopt))
                                    t1.FStar_Syntax_Syntax.pos
                                   in
                                norm cfg
                                  (((FStar_Pervasives_Native.Some b), c) ::
                                  env1) stack_rest body1))))
                | (Cfg cfg1)::stack2 -> norm cfg1 env1 stack2 t1
                | (MemoLazy r)::stack2 ->
                    (set_memo cfg r (env1, t1);
                     FStar_TypeChecker_Cfg.log cfg
                       (fun uu____10745  ->
                          let uu____10746 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10746);
                     norm cfg env1 stack2 t1)
                | (Match uu____10749)::uu____10750 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10765 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10765 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____10801  -> dummy :: env2) env1)
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
                                          let uu____10845 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10845)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_10853 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_10853.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_10853.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10854 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10860  ->
                                 let uu____10861 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10861);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_10876 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_10876.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_10876.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_10876.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_10876.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_10876.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_10876.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_10876.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_10876.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Debug uu____10880)::uu____10881 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10892 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10892 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____10928  -> dummy :: env2) env1)
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
                                          let uu____10972 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10972)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_10980 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_10980.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_10980.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10981 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10987  ->
                                 let uu____10988 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10988);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11003 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11003.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11003.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11003.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11003.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11003.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11003.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11003.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11003.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11007)::uu____11008 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11021 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11021 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11057  -> dummy :: env2) env1)
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
                                          let uu____11101 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11101)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11109 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11109.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11109.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11110 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11116  ->
                                 let uu____11117 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11117);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11132 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11132.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11132.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11132.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11132.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11132.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11132.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11132.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11132.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11136)::uu____11137 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11152 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11152 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11188  -> dummy :: env2) env1)
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
                                          let uu____11232 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11232)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11240 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11240.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11240.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11241 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11247  ->
                                 let uu____11248 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11248);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11263 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11263.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11263.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11263.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11263.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11263.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11263.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11263.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11263.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11267)::uu____11268 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11283 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11283 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11319  -> dummy :: env2) env1)
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
                                          let uu____11363 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11363)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11371 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11371.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11371.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11372 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11378  ->
                                 let uu____11379 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11379);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11394 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11394.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11394.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11394.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11394.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11394.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11394.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11394.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11394.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (CBVApp uu____11398)::uu____11399 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11414 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11414 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11450  -> dummy :: env2) env1)
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
                                          let uu____11494 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11494)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11502 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11502.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11502.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11503 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11509  ->
                                 let uu____11510 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11510);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11525 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11525.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11525.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11525.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11525.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11525.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11525.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11525.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11525.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____11529)::uu____11530 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11549 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11549 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11585  -> dummy :: env2) env1)
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
                                          let uu____11629 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11629)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11637 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11637.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11637.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11638 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11644  ->
                                 let uu____11645 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11645);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11660 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11660.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11660.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11660.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11660.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11660.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11660.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11660.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11660.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | [] ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11668 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11668 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11704  -> dummy :: env2) env1)
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
                                          let uu____11748 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11748)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11756 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11756.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11756.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11757 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11763  ->
                                 let uu____11764 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11764);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11779 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11779.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11779.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11779.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11779.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11779.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11779.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11779.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11779.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head,args) ->
               let strict_args =
                 let uu____11815 =
                   let uu____11816 = FStar_Syntax_Util.un_uinst head  in
                   uu____11816.FStar_Syntax_Syntax.n  in
                 match uu____11815 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11825 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____11846  ->
                              fun stack2  ->
                                match uu____11846 with
                                | (a,aq) ->
                                    let uu____11858 =
                                      let uu____11859 =
                                        let uu____11866 =
                                          let uu____11867 =
                                            let uu____11899 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env1, a, uu____11899, false)  in
                                          Clos uu____11867  in
                                        (uu____11866, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11859  in
                                    uu____11858 :: stack2) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11967  ->
                          let uu____11968 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11968);
                     norm cfg env1 stack2 head)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____12019  ->
                              match uu____12019 with
                              | (a,i) ->
                                  let uu____12030 = norm cfg env1 [] a  in
                                  (uu____12030, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____12036 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____12051 = FStar_List.nth norm_args i
                                    in
                                 match uu____12051 with
                                 | (arg_i,uu____12062) ->
                                     let uu____12063 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____12063 with
                                      | (head1,uu____12082) ->
                                          let uu____12107 =
                                            let uu____12108 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____12108.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____12107 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____12112 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____12115 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____12115
                                           | uu____12116 -> false)))))
                       in
                    if uu____12036
                    then
                      let stack2 =
                        FStar_All.pipe_right stack1
                          (FStar_List.fold_right
                             (fun uu____12133  ->
                                fun stack2  ->
                                  match uu____12133 with
                                  | (a,aq) ->
                                      let uu____12145 =
                                        let uu____12146 =
                                          let uu____12153 =
                                            let uu____12154 =
                                              let uu____12186 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env1, a, uu____12186, false)
                                               in
                                            Clos uu____12154  in
                                          (uu____12153, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____12146  in
                                      uu____12145 :: stack2) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12268  ->
                            let uu____12269 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12269);
                       norm cfg env1 stack2 head)
                    else
                      (let head1 = closure_as_term cfg env1 head  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head1 norm_args
                           FStar_Pervasives_Native.None
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env1 stack1 term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12289) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
               -> norm cfg env1 stack1 x.FStar_Syntax_Syntax.sort
           | FStar_Syntax_Syntax.Tm_refine (x,f) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 (match (env1, stack1) with
                  | ([],[]) ->
                      let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort
                         in
                      let t2 =
                        mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___1511_12334 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1511_12334.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1511_12334.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env1 stack1 t2
                  | uu____12335 ->
                      let uu____12350 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 uu____12350)
               else
                 (let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12354 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12354 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env1) [] f1  in
                      let t2 =
                        let uu____12385 =
                          let uu____12386 =
                            let uu____12393 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1520_12399 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1520_12399.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1520_12399.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12393)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12386  in
                        mk uu____12385 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12423 = closure_as_term cfg env1 t1  in
                 rebuild cfg env1 stack1 uu____12423
               else
                 (let uu____12426 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12426 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12434 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env2  ->
                                  fun uu____12460  -> dummy :: env2) env1)
                           in
                        norm_comp cfg uu____12434 c1  in
                      let t2 =
                        let uu____12484 = norm_binders cfg env1 bs1  in
                        FStar_Syntax_Util.arrow uu____12484 c2  in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env1 stack1 t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12597)::uu____12598 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12611  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (Arg uu____12613)::uu____12614 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12625  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (App
                    (uu____12627,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12628;
                                   FStar_Syntax_Syntax.vars = uu____12629;_},uu____12630,uu____12631))::uu____12632
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12639  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (MemoLazy uu____12641)::uu____12642 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12653  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | uu____12655 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12658  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env1 [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12663  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12689 = norm cfg env1 [] t2  in
                             FStar_Util.Inl uu____12689
                         | FStar_Util.Inr c ->
                             let uu____12703 = norm_comp cfg env1 c  in
                             FStar_Util.Inr uu____12703
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env1 [])  in
                       match stack1 with
                       | (Cfg cfg1)::stack2 ->
                           let t2 =
                             let uu____12726 =
                               let uu____12727 =
                                 let uu____12754 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12754, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12727
                                in
                             mk uu____12726 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env1 stack2 t2
                       | uu____12789 ->
                           let uu____12790 =
                             let uu____12791 =
                               let uu____12792 =
                                 let uu____12819 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12819, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12792
                                in
                             mk uu____12791 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env1 stack1 uu____12790))))
           | FStar_Syntax_Syntax.Tm_match (head,branches1) ->
               let stack2 =
                 (Match (env1, branches1, cfg, (t1.FStar_Syntax_Syntax.pos)))
                 :: stack1  in
               if
                 ((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                    &&
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weakly_reduce_scrutinee)
                   &&
                   (Prims.op_Negation
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak)
               then
                 let cfg' =
                   let uu___1599_12897 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1601_12900 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1601_12900.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1599_12897.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1599_12897.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1599_12897.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1599_12897.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1599_12897.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1599_12897.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1599_12897.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1599_12897.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 norm cfg' env1 ((Cfg cfg) :: stack2) head
               else norm cfg env1 stack2 head
           | FStar_Syntax_Syntax.Tm_let ((b,lbs),lbody) when
               (FStar_Syntax_Syntax.is_top_level lbs) &&
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               ->
               let lbs1 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu____12941 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12941 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1614_12961 = cfg  in
                               let uu____12962 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1614_12961.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12962;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1614_12961.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1614_12961.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1614_12961.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1614_12961.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1614_12961.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1614_12961.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1614_12961.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____12969 =
                                 let uu____12970 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env1 [] uu____12970  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12969
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1621_12973 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1621_12973.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1621_12973.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1621_12973.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1621_12973.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12974 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env1 stack1 uu____12974
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12987,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12988;
                               FStar_Syntax_Syntax.lbunivs = uu____12989;
                               FStar_Syntax_Syntax.lbtyp = uu____12990;
                               FStar_Syntax_Syntax.lbeff = uu____12991;
                               FStar_Syntax_Syntax.lbdef = uu____12992;
                               FStar_Syntax_Syntax.lbattrs = uu____12993;
                               FStar_Syntax_Syntax.lbpos = uu____12994;_}::uu____12995),uu____12996)
               -> rebuild cfg env1 stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let uu____13041 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
               if uu____13041
               then
                 let binder =
                   let uu____13045 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13045  in
                 let env2 =
                   let uu____13055 =
                     let uu____13062 =
                       let uu____13063 =
                         let uu____13095 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env1, (lb.FStar_Syntax_Syntax.lbdef), uu____13095,
                           false)
                          in
                       Clos uu____13063  in
                     ((FStar_Pervasives_Native.Some binder), uu____13062)  in
                   uu____13055 :: env1  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____13170  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env2 stack1 body)
               else
                 (let uu____13174 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu____13177 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff
                          in
                       FStar_Syntax_Util.is_div_effect uu____13177)
                     in
                  if uu____13174
                  then
                    let ffun =
                      let uu____13182 =
                        let uu____13189 =
                          let uu____13190 =
                            let uu____13209 =
                              let uu____13218 =
                                let uu____13225 =
                                  FStar_All.pipe_right
                                    lb.FStar_Syntax_Syntax.lbname
                                    FStar_Util.left
                                   in
                                FStar_Syntax_Syntax.mk_binder uu____13225  in
                              [uu____13218]  in
                            (uu____13209, body, FStar_Pervasives_Native.None)
                             in
                          FStar_Syntax_Syntax.Tm_abs uu____13190  in
                        FStar_Syntax_Syntax.mk uu____13189  in
                      uu____13182 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    let stack2 =
                      (CBVApp
                         (env1, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack1  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____13259  ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env1 stack2 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____13266  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____13268 = closure_as_term cfg env1 t1  in
                        rebuild cfg env1 stack1 uu____13268))
                    else
                      (let uu____13271 =
                         let uu____13276 =
                           let uu____13277 =
                             let uu____13284 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____13284
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____13277]  in
                         FStar_Syntax_Subst.open_term uu____13276 body  in
                       match uu____13271 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____13311  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____13320 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____13320  in
                               FStar_Util.Inl
                                 (let uu___1667_13336 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1667_13336.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1667_13336.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____13339  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1672_13342 = lb  in
                                let uu____13343 =
                                  norm cfg env1 []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____13346 =
                                  FStar_List.map (norm cfg env1 [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1672_13342.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1672_13342.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____13343;
                                  FStar_Syntax_Syntax.lbattrs = uu____13346;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1672_13342.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____13381  -> dummy :: env2)
                                     env1)
                                 in
                              let stack2 = (Cfg cfg) :: stack1  in
                              let cfg1 =
                                let uu___1679_13406 = cfg  in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1679_13406.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1679_13406.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1679_13406.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1679_13406.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1679_13406.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1679_13406.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1679_13406.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1679_13406.FStar_TypeChecker_Cfg.reifying)
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____13410  ->
                                   FStar_Util.print_string
                                     "+++ Normalizing Tm_let -- body\n");
                              norm cfg1 env'
                                ((Let
                                    (env1, bs, lb1,
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack2) body1)))))
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
               let uu____13431 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13431 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp
                              in
                           let lbname =
                             let uu____13467 =
                               let uu___1695_13468 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1695_13468.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1695_13468.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13467  in
                           let uu____13469 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13469 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env1 xs  in
                               let env2 =
                                 let uu____13495 =
                                   FStar_List.map (fun uu____13517  -> dummy)
                                     xs1
                                    in
                                 let uu____13524 =
                                   let uu____13533 =
                                     FStar_List.map
                                       (fun uu____13549  -> dummy) lbs1
                                      in
                                   FStar_List.append uu____13533 env1  in
                                 FStar_List.append uu____13495 uu____13524
                                  in
                               let def_body1 = norm cfg env2 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13569 =
                                       let uu___1709_13570 = rc  in
                                       let uu____13571 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env2 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1709_13570.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13571;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1709_13570.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13569
                                 | uu____13580 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1714_13586 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1714_13586.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1714_13586.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1714_13586.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1714_13586.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13596 =
                        FStar_List.map (fun uu____13612  -> dummy) lbs2  in
                      FStar_List.append uu____13596 env1  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13620 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13620 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1723_13636 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1723_13636.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1723_13636.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env1 stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu____13670 = closure_as_term cfg env1 t1  in
               rebuild cfg env1 stack1 uu____13670
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13691 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13769  ->
                        match uu____13769 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1739_13894 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1739_13894.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1739_13894.FStar_Syntax_Syntax.sort)
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
                                (Clos (env1, fix_f_i, memo, true)))
                              :: rec_env  in
                            (rec_env1, (memo :: memos), (i + Prims.int_one)))
                   (FStar_Pervasives_Native.snd lbs)
                   (env1, [], Prims.int_zero)
                  in
               (match uu____13691 with
                | (rec_env,memos,uu____14085) ->
                    let uu____14140 =
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
                           fun env2  ->
                             let uu____14389 =
                               let uu____14396 =
                                 let uu____14397 =
                                   let uu____14429 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14429, false)
                                    in
                                 Clos uu____14397  in
                               (FStar_Pervasives_Native.None, uu____14396)
                                in
                             uu____14389 :: env2)
                        (FStar_Pervasives_Native.snd lbs) env1
                       in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14514  ->
                     let uu____14515 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14515);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14539 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env1 stack1 head
                     else
                       (match stack1 with
                        | uu____14543::uu____14544 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14549) ->
                                 norm cfg env1 ((Meta (env1, m, r)) ::
                                   stack1) head
                             | FStar_Syntax_Syntax.Meta_pattern (names,args)
                                 ->
                                 let args1 = norm_pattern_args cfg env1 args
                                    in
                                 let names1 =
                                   FStar_All.pipe_right names
                                     (FStar_List.map (norm cfg env1 []))
                                    in
                                 norm cfg env1
                                   ((Meta
                                       (env1,
                                         (FStar_Syntax_Syntax.Meta_pattern
                                            (names1, args1)),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack1) head
                             | uu____14628 -> norm cfg env1 stack1 head)
                        | [] ->
                            let head1 = norm cfg env1 [] head  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern (names,args)
                                  ->
                                  let names1 =
                                    FStar_All.pipe_right names
                                      (FStar_List.map (norm cfg env1 []))
                                     in
                                  let uu____14676 =
                                    let uu____14697 =
                                      norm_pattern_args cfg env1 args  in
                                    (names1, uu____14697)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14676
                              | uu____14726 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head1, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env1 stack1 t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14732 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env1 stack1 t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14748 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14762 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14776 =
                        let uu____14778 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14780 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14778 uu____14780
                         in
                      failwith uu____14776
                    else
                      (let uu____14785 = inline_closure_env cfg env1 [] t2
                          in
                       rebuild cfg env1 stack1 uu____14785)
                | uu____14786 -> norm cfg env1 stack1 t2))

and (do_unfold_fv :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      stack_elt Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_TypeChecker_Env.qninfo ->
            FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun t0  ->
          fun qninfo  ->
            fun f  ->
              let uu____14795 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14795 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14809  ->
                        let uu____14810 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14810);
                   rebuild cfg env1 stack1 t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14823  ->
                        let uu____14824 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14826 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14824 uu____14826);
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
                    let n = FStar_List.length us  in
                    if n > Prims.int_zero
                    then
                      match stack1 with
                      | (UnivArgs (us',uu____14839))::stack2 ->
                          ((let uu____14848 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14848
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14856 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14856) us'
                            else ());
                           (let env2 =
                              FStar_All.pipe_right us'
                                (FStar_List.fold_left
                                   (fun env2  ->
                                      fun u  ->
                                        (FStar_Pervasives_Native.None,
                                          (Univ u))
                                        :: env2) env1)
                               in
                            norm cfg env2 stack2 t1))
                      | uu____14892 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env1 stack1 t1
                      | uu____14895 ->
                          let uu____14898 =
                            let uu____14900 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14900
                             in
                          failwith uu____14898
                    else norm cfg env1 stack1 t1))

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
    fun env1  ->
      fun stack1  ->
        fun head  ->
          fun m  ->
            fun t  ->
              let t1 = norm cfg env1 [] t  in
              let uu____14920 =
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
                    let uu___1850_14938 = cfg  in
                    let uu____14939 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps
                       in
                    {
                      FStar_TypeChecker_Cfg.steps = uu____14939;
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1850_14938.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1850_14938.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        [FStar_TypeChecker_Env.InliningDelta;
                        FStar_TypeChecker_Env.Eager_unfolding_only];
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1850_14938.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1850_14938.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1850_14938.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1850_14938.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1850_14938.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  (cfg', ((Cfg cfg) :: stack1))
                else (cfg, stack1)  in
              match uu____14920 with
              | (cfg1,stack2) ->
                  let metadata =
                    match m with
                    | FStar_Util.Inl m1 ->
                        FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                    | FStar_Util.Inr (m1,m') ->
                        FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1)
                     in
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
  fun fallback  ->
    fun cfg  ->
      fun env1  ->
        fun stack1  ->
          fun top  ->
            fun m  ->
              fun t  ->
                (match stack1 with
                 | (App
                     (uu____14980,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14981;
                                    FStar_Syntax_Syntax.vars = uu____14982;_},uu____14983,uu____14984))::uu____14985
                     -> ()
                 | uu____14990 ->
                     let uu____14993 =
                       let uu____14995 = stack_to_string stack1  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14995
                        in
                     failwith uu____14993);
                (let top0 = top  in
                 let top1 = FStar_Syntax_Util.unascribe top  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____15004  ->
                      let uu____15005 = FStar_Syntax_Print.tag_of_term top1
                         in
                      let uu____15007 =
                        FStar_Syntax_Print.term_to_string top1  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____15005
                        uu____15007);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1  in
                  let uu____15011 =
                    let uu____15012 = FStar_Syntax_Subst.compress top2  in
                    uu____15012.FStar_Syntax_Syntax.n  in
                  match uu____15011 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m
                         in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name
                         in
                      let uu____15034 =
                        let uu____15043 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr
                           in
                        FStar_All.pipe_right uu____15043 FStar_Util.must  in
                      (match uu____15034 with
                       | (uu____15058,repr) ->
                           let uu____15068 =
                             let uu____15075 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr
                                in
                             FStar_All.pipe_right uu____15075 FStar_Util.must
                              in
                           (match uu____15068 with
                            | (uu____15112,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15118 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15129 =
                                         let uu____15130 =
                                           FStar_Syntax_Subst.compress e  in
                                         uu____15130.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15129 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15136,uu____15137))
                                           ->
                                           let uu____15146 =
                                             let uu____15147 =
                                               FStar_Syntax_Subst.compress e1
                                                in
                                             uu____15147.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____15146 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15153,msrc,uu____15155))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15164 =
                                                  FStar_Syntax_Subst.compress
                                                    e2
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____15164
                                            | uu____15165 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15166 ->
                                           FStar_Pervasives_Native.None
                                        in
                                     let uu____15167 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     (match uu____15167 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___1929_15172 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___1929_15172.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___1929_15172.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___1929_15172.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e;
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___1929_15172.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___1929_15172.FStar_Syntax_Syntax.lbpos)
                                            }  in
                                          let uu____15173 =
                                            FStar_List.tl stack1  in
                                          let uu____15174 =
                                            let uu____15175 =
                                              let uu____15182 =
                                                let uu____15183 =
                                                  let uu____15197 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body
                                                     in
                                                  ((false, [lb1]),
                                                    uu____15197)
                                                   in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15183
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15182
                                               in
                                            uu____15175
                                              FStar_Pervasives_Native.None
                                              top2.FStar_Syntax_Syntax.pos
                                             in
                                          norm cfg env1 uu____15173
                                            uu____15174
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15213 =
                                            let uu____15215 = is_return body
                                               in
                                            match uu____15215 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15220;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15221;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15224 -> false  in
                                          if uu____15213
                                          then
                                            norm cfg env1 stack1
                                              lb.FStar_Syntax_Syntax.lbdef
                                          else
                                            (let rng =
                                               top2.FStar_Syntax_Syntax.pos
                                                in
                                             let head =
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Util.mk_reify
                                                 lb.FStar_Syntax_Syntax.lbdef
                                                in
                                             let uu____15239 =
                                               let bv =
                                                 FStar_Syntax_Syntax.new_bv
                                                   FStar_Pervasives_Native.None
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let lb1 =
                                                 let uu____15248 =
                                                   let uu____15251 =
                                                     let uu____15262 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         x.FStar_Syntax_Syntax.sort
                                                        in
                                                     [uu____15262]  in
                                                   FStar_Syntax_Util.mk_app
                                                     repr uu____15251
                                                    in
                                                 let uu____15287 =
                                                   let uu____15288 =
                                                     FStar_TypeChecker_Env.is_total_effect
                                                       cfg.FStar_TypeChecker_Cfg.tcenv
                                                       eff_name
                                                      in
                                                   if uu____15288
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
                                                     = uu____15248;
                                                   FStar_Syntax_Syntax.lbeff
                                                     = uu____15287;
                                                   FStar_Syntax_Syntax.lbdef
                                                     = head;
                                                   FStar_Syntax_Syntax.lbattrs
                                                     = [];
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (head.FStar_Syntax_Syntax.pos)
                                                 }  in
                                               let uu____15295 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   bv
                                                  in
                                               (lb1, bv, uu____15295)  in
                                             match uu____15239 with
                                             | (lb_head,head_bv,head1) ->
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
                                                   let uu____15312 =
                                                     let uu____15319 =
                                                       let uu____15320 =
                                                         let uu____15339 =
                                                           let uu____15348 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x
                                                              in
                                                           [uu____15348]  in
                                                         (uu____15339, body1,
                                                           (FStar_Pervasives_Native.Some
                                                              body_rc))
                                                          in
                                                       FStar_Syntax_Syntax.Tm_abs
                                                         uu____15320
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15319
                                                      in
                                                   uu____15312
                                                     FStar_Pervasives_Native.None
                                                     body1.FStar_Syntax_Syntax.pos
                                                    in
                                                 let close =
                                                   closure_as_term cfg env1
                                                    in
                                                 let bind_inst =
                                                   let uu____15387 =
                                                     let uu____15388 =
                                                       FStar_Syntax_Subst.compress
                                                         bind_repr
                                                        in
                                                     uu____15388.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____15387 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (bind,uu____15394::uu____15395::[])
                                                       ->
                                                       let uu____15400 =
                                                         let uu____15407 =
                                                           let uu____15408 =
                                                             let uu____15415
                                                               =
                                                               let uu____15416
                                                                 =
                                                                 let uu____15417
                                                                   =
                                                                   close
                                                                    lb.FStar_Syntax_Syntax.lbtyp
                                                                    in
                                                                 (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                                   uu____15417
                                                                  in
                                                               let uu____15418
                                                                 =
                                                                 let uu____15421
                                                                   =
                                                                   let uu____15422
                                                                    = 
                                                                    close t
                                                                     in
                                                                   (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                    cfg.FStar_TypeChecker_Cfg.tcenv
                                                                    uu____15422
                                                                    in
                                                                 [uu____15421]
                                                                  in
                                                               uu____15416 ::
                                                                 uu____15418
                                                                in
                                                             (bind,
                                                               uu____15415)
                                                              in
                                                           FStar_Syntax_Syntax.Tm_uinst
                                                             uu____15408
                                                            in
                                                         FStar_Syntax_Syntax.mk
                                                           uu____15407
                                                          in
                                                       uu____15400
                                                         FStar_Pervasives_Native.None
                                                         rng
                                                   | uu____15425 ->
                                                       failwith
                                                         "NIY : Reification of indexed effects"
                                                    in
                                                 let maybe_range_arg =
                                                   let uu____15440 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____15440
                                                   then
                                                     let uu____15453 =
                                                       let uu____15462 =
                                                         FStar_TypeChecker_Cfg.embed_simple
                                                           FStar_Syntax_Embeddings.e_range
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                          in
                                                       FStar_Syntax_Syntax.as_arg
                                                         uu____15462
                                                        in
                                                     let uu____15463 =
                                                       let uu____15474 =
                                                         let uu____15483 =
                                                           FStar_TypeChecker_Cfg.embed_simple
                                                             FStar_Syntax_Embeddings.e_range
                                                             body2.FStar_Syntax_Syntax.pos
                                                             body2.FStar_Syntax_Syntax.pos
                                                            in
                                                         FStar_Syntax_Syntax.as_arg
                                                           uu____15483
                                                          in
                                                       [uu____15474]  in
                                                     uu____15453 ::
                                                       uu____15463
                                                   else []  in
                                                 let reified =
                                                   let args =
                                                     let uu____15532 =
                                                       FStar_Syntax_Util.is_layered
                                                         ed
                                                        in
                                                     if uu____15532
                                                     then
                                                       let unit_args =
                                                         let uu____15556 =
                                                           let uu____15557 =
                                                             let uu____15560
                                                               =
                                                               let uu____15561
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15561
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15560
                                                               FStar_Syntax_Subst.compress
                                                              in
                                                           uu____15557.FStar_Syntax_Syntax.n
                                                            in
                                                         match uu____15556
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_arrow
                                                             (uu____15602::uu____15603::bs,uu____15605)
                                                             when
                                                             (FStar_List.length
                                                                bs)
                                                               >=
                                                               (Prims.of_int (2))
                                                             ->
                                                             let uu____15657
                                                               =
                                                               let uu____15666
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   bs
                                                                   (FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2))))
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15666
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15657
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____15797
                                                                     ->
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.unit_const))
                                                         | uu____15804 ->
                                                             let uu____15805
                                                               =
                                                               let uu____15811
                                                                 =
                                                                 let uu____15813
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    ed.FStar_Syntax_Syntax.mname
                                                                    in
                                                                 let uu____15815
                                                                   =
                                                                   let uu____15817
                                                                    =
                                                                    let uu____15818
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    ed
                                                                    FStar_Syntax_Util.get_bind_vc_combinator
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15818
                                                                    FStar_Pervasives_Native.snd
                                                                     in
                                                                   FStar_All.pipe_right
                                                                    uu____15817
                                                                    FStar_Syntax_Print.term_to_string
                                                                    in
                                                                 FStar_Util.format2
                                                                   "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                                   uu____15813
                                                                   uu____15815
                                                                  in
                                                               (FStar_Errors.Fatal_UnexpectedEffect,
                                                                 uu____15811)
                                                                in
                                                             FStar_Errors.raise_error
                                                               uu____15805
                                                               rng
                                                          in
                                                       let uu____15852 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let uu____15861 =
                                                         let uu____15872 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t
                                                            in
                                                         let uu____15881 =
                                                           let uu____15892 =
                                                             let uu____15903
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head1
                                                                in
                                                             let uu____15912
                                                               =
                                                               let uu____15923
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   body2
                                                                  in
                                                               [uu____15923]
                                                                in
                                                             uu____15903 ::
                                                               uu____15912
                                                              in
                                                           FStar_List.append
                                                             unit_args
                                                             uu____15892
                                                            in
                                                         uu____15872 ::
                                                           uu____15881
                                                          in
                                                       uu____15852 ::
                                                         uu____15861
                                                     else
                                                       (let uu____15982 =
                                                          let uu____15993 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              lb.FStar_Syntax_Syntax.lbtyp
                                                             in
                                                          let uu____16002 =
                                                            let uu____16013 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t
                                                               in
                                                            [uu____16013]  in
                                                          uu____15993 ::
                                                            uu____16002
                                                           in
                                                        let uu____16046 =
                                                          let uu____16057 =
                                                            let uu____16068 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            let uu____16077 =
                                                              let uu____16088
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  head1
                                                                 in
                                                              let uu____16097
                                                                =
                                                                let uu____16108
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.tun
                                                                   in
                                                                let uu____16117
                                                                  =
                                                                  let uu____16128
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    body2  in
                                                                  [uu____16128]
                                                                   in
                                                                uu____16108
                                                                  ::
                                                                  uu____16117
                                                                 in
                                                              uu____16088 ::
                                                                uu____16097
                                                               in
                                                            uu____16068 ::
                                                              uu____16077
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____16057
                                                           in
                                                        FStar_List.append
                                                          uu____15982
                                                          uu____16046)
                                                      in
                                                   let uu____16193 =
                                                     let uu____16200 =
                                                       let uu____16201 =
                                                         let uu____16215 =
                                                           let uu____16218 =
                                                             let uu____16225
                                                               =
                                                               let uu____16226
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   head_bv
                                                                  in
                                                               [uu____16226]
                                                                in
                                                             FStar_Syntax_Subst.close
                                                               uu____16225
                                                              in
                                                           let uu____16245 =
                                                             FStar_Syntax_Syntax.mk
                                                               (FStar_Syntax_Syntax.Tm_app
                                                                  (bind_inst,
                                                                    args))
                                                               FStar_Pervasives_Native.None
                                                               rng
                                                              in
                                                           FStar_All.pipe_left
                                                             uu____16218
                                                             uu____16245
                                                            in
                                                         ((false, [lb_head]),
                                                           uu____16215)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_let
                                                         uu____16201
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____16200
                                                      in
                                                   uu____16193
                                                     FStar_Pervasives_Native.None
                                                     rng
                                                    in
                                                 (FStar_TypeChecker_Cfg.log
                                                    cfg
                                                    (fun uu____16277  ->
                                                       let uu____16278 =
                                                         FStar_Syntax_Print.term_to_string
                                                           top0
                                                          in
                                                       let uu____16280 =
                                                         FStar_Syntax_Print.term_to_string
                                                           reified
                                                          in
                                                       FStar_Util.print2
                                                         "Reified (1) <%s> to %s\n"
                                                         uu____16278
                                                         uu____16280);
                                                  (let uu____16283 =
                                                     FStar_List.tl stack1  in
                                                   norm cfg env1 uu____16283
                                                     reified)))))))
                  | FStar_Syntax_Syntax.Tm_app (head,args) ->
                      ((let uu____16311 = FStar_Options.defensive ()  in
                        if uu____16311
                        then
                          let is_arg_impure uu____16326 =
                            match uu____16326 with
                            | (e,q) ->
                                let uu____16340 =
                                  let uu____16341 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16341.FStar_Syntax_Syntax.n  in
                                (match uu____16340 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____16357 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____16357
                                 | uu____16359 -> false)
                             in
                          let uu____16361 =
                            let uu____16363 =
                              let uu____16374 =
                                FStar_Syntax_Syntax.as_arg head  in
                              uu____16374 :: args  in
                            FStar_Util.for_some is_arg_impure uu____16363  in
                          (if uu____16361
                           then
                             let uu____16400 =
                               let uu____16406 =
                                 let uu____16408 =
                                   FStar_Syntax_Print.term_to_string top2  in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____16408
                                  in
                               (FStar_Errors.Warning_Defensive, uu____16406)
                                in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu____16400
                           else ())
                        else ());
                       (let fallback1 uu____16421 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16425  ->
                               let uu____16426 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____16426 "");
                          (let uu____16430 = FStar_List.tl stack1  in
                           let uu____16431 = FStar_Syntax_Util.mk_reify top2
                              in
                           norm cfg env1 uu____16430 uu____16431)
                           in
                        let fallback2 uu____16437 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16441  ->
                               let uu____16442 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____16442 "");
                          (let uu____16446 = FStar_List.tl stack1  in
                           let uu____16447 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env1 uu____16446 uu____16447)
                           in
                        let uu____16452 =
                          let uu____16453 = FStar_Syntax_Util.un_uinst head
                             in
                          uu____16453.FStar_Syntax_Syntax.n  in
                        match uu____16452 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____16459 =
                              let uu____16461 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____16461  in
                            if uu____16459
                            then fallback1 ()
                            else
                              (let uu____16466 =
                                 let uu____16468 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____16468  in
                               if uu____16466
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____16485 =
                                      let uu____16490 =
                                        FStar_Syntax_Util.mk_reify head  in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____16490 args
                                       in
                                    uu____16485 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____16491 = FStar_List.tl stack1  in
                                  norm cfg env1 uu____16491 t1))
                        | uu____16492 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____16494) ->
                      do_reify_monadic fallback cfg env1 stack1 e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____16518 = closure_as_term cfg env1 t'  in
                        reify_lift cfg e msrc mtgt uu____16518  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____16522  ->
                            let uu____16523 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____16523);
                       (let uu____16526 = FStar_List.tl stack1  in
                        norm cfg env1 uu____16526 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches1) ->
                      let branches2 =
                        FStar_All.pipe_right branches1
                          (FStar_List.map
                             (fun uu____16647  ->
                                match uu____16647 with
                                | (pat,wopt,tm) ->
                                    let uu____16695 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16695)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches2))
                          top2.FStar_Syntax_Syntax.pos
                         in
                      let uu____16727 = FStar_List.tl stack1  in
                      norm cfg env1 uu____16727 tm
                  | uu____16728 -> fallback ()))

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
            let env1 = cfg.FStar_TypeChecker_Cfg.tcenv  in
            FStar_TypeChecker_Cfg.log cfg
              (fun uu____16742  ->
                 let uu____16743 = FStar_Ident.string_of_lid msrc  in
                 let uu____16745 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16747 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16743
                   uu____16745 uu____16747);
            (let uu____16750 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16753 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env1)
                     in
                  Prims.op_Negation uu____16753)
                in
             if uu____16750
             then
               let ed =
                 let uu____16758 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env1 uu____16758  in
               let uu____16759 =
                 let uu____16768 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 FStar_All.pipe_right uu____16768 FStar_Util.must  in
               match uu____16759 with
               | (uu____16815,repr) ->
                   let uu____16825 =
                     let uu____16834 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr
                        in
                     FStar_All.pipe_right uu____16834 FStar_Util.must  in
                   (match uu____16825 with
                    | (uu____16881,return_repr) ->
                        let return_inst =
                          let uu____16894 =
                            let uu____16895 =
                              FStar_Syntax_Subst.compress return_repr  in
                            uu____16895.FStar_Syntax_Syntax.n  in
                          match uu____16894 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm,uu____16901::[]) ->
                              let uu____16906 =
                                let uu____16913 =
                                  let uu____16914 =
                                    let uu____16921 =
                                      let uu____16922 =
                                        env1.FStar_TypeChecker_Env.universe_of
                                          env1 t
                                         in
                                      [uu____16922]  in
                                    (return_tm, uu____16921)  in
                                  FStar_Syntax_Syntax.Tm_uinst uu____16914
                                   in
                                FStar_Syntax_Syntax.mk uu____16913  in
                              uu____16906 FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                          | uu____16925 ->
                              failwith "NIY : Reification of indexed effects"
                           in
                        let uu____16929 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t
                             in
                          let lb =
                            let uu____16940 =
                              let uu____16943 =
                                let uu____16954 =
                                  FStar_Syntax_Syntax.as_arg t  in
                                [uu____16954]  in
                              FStar_Syntax_Util.mk_app repr uu____16943  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Util.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu____16940;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            }  in
                          let uu____16981 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (lb, bv, uu____16981)  in
                        (match uu____16929 with
                         | (lb_e,e_bv,e1) ->
                             let uu____16993 =
                               let uu____17000 =
                                 let uu____17001 =
                                   let uu____17015 =
                                     let uu____17018 =
                                       let uu____17025 =
                                         let uu____17026 =
                                           FStar_Syntax_Syntax.mk_binder e_bv
                                            in
                                         [uu____17026]  in
                                       FStar_Syntax_Subst.close uu____17025
                                        in
                                     let uu____17045 =
                                       let uu____17046 =
                                         let uu____17053 =
                                           let uu____17054 =
                                             let uu____17071 =
                                               let uu____17082 =
                                                 FStar_Syntax_Syntax.as_arg t
                                                  in
                                               let uu____17091 =
                                                 let uu____17102 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     e1
                                                    in
                                                 [uu____17102]  in
                                               uu____17082 :: uu____17091  in
                                             (return_inst, uu____17071)  in
                                           FStar_Syntax_Syntax.Tm_app
                                             uu____17054
                                            in
                                         FStar_Syntax_Syntax.mk uu____17053
                                          in
                                       uu____17046
                                         FStar_Pervasives_Native.None
                                         e1.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_All.pipe_left uu____17018
                                       uu____17045
                                      in
                                   ((false, [lb_e]), uu____17015)  in
                                 FStar_Syntax_Syntax.Tm_let uu____17001  in
                               FStar_Syntax_Syntax.mk uu____17000  in
                             uu____16993 FStar_Pervasives_Native.None
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu____17164 =
                  FStar_TypeChecker_Env.monad_leq env1 msrc mtgt  in
                match uu____17164 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17167 =
                      let uu____17169 = FStar_Ident.string_of_lid msrc  in
                      let uu____17171 = FStar_Ident.string_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17169 uu____17171
                       in
                    failwith uu____17167
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17174;
                      FStar_TypeChecker_Env.mtarget = uu____17175;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17176;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17196 =
                      let uu____17198 = FStar_Ident.string_of_lid msrc  in
                      let uu____17200 = FStar_Ident.string_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17198 uu____17200
                       in
                    failwith uu____17196
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17203;
                      FStar_TypeChecker_Env.mtarget = uu____17204;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17205;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____17236 =
                        FStar_TypeChecker_Env.is_reifiable_effect env1 msrc
                         in
                      if uu____17236
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____17241 =
                           let uu____17248 =
                             let uu____17249 =
                               let uu____17268 =
                                 let uu____17277 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____17277]  in
                               (uu____17268, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____17249  in
                           FStar_Syntax_Syntax.mk uu____17248  in
                         uu____17241 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____17310 =
                      env1.FStar_TypeChecker_Env.universe_of env1 t  in
                    lift uu____17310 t e1))

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
    fun env1  ->
      fun args  ->
        FStar_All.pipe_right args
          (FStar_List.map
             (FStar_List.map
                (fun uu____17380  ->
                   match uu____17380 with
                   | (a,imp) ->
                       let uu____17399 = norm cfg env1 [] a  in
                       (uu____17399, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env1  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17409  ->
             let uu____17410 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17412 =
               FStar_Util.string_of_int (FStar_List.length env1)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17410 uu____17412);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env1 [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17438 = norm_universe cfg env1 u  in
                   FStar_All.pipe_left
                     (fun uu____17441  ->
                        FStar_Pervasives_Native.Some uu____17441) uu____17438
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2110_17442 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2110_17442.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2110_17442.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env1 [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17464 = norm_universe cfg env1 u  in
                   FStar_All.pipe_left
                     (fun uu____17467  ->
                        FStar_Pervasives_Native.Some uu____17467) uu____17464
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2121_17468 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2121_17468.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2121_17468.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17513  ->
                      match uu____17513 with
                      | (a,i) ->
                          let uu____17533 = norm cfg env1 [] a  in
                          (uu____17533, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17555  ->
                       match uu___14_17555 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17559 = norm cfg env1 [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17559
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env1)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env1 [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2138_17567 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2140_17570 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2140_17570.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2138_17567.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2138_17567.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env1  ->
      fun b  ->
        let uu____17574 = b  in
        match uu____17574 with
        | (x,imp) ->
            let x1 =
              let uu___2148_17582 = x  in
              let uu____17583 = norm cfg env1 [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2148_17582.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2148_17582.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17583
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____17594 =
                    let uu____17595 = closure_as_term cfg env1 t  in
                    FStar_Syntax_Syntax.Meta uu____17595  in
                  FStar_Pervasives_Native.Some uu____17594
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env1  ->
      fun bs  ->
        let uu____17606 =
          FStar_List.fold_left
            (fun uu____17640  ->
               fun b  ->
                 match uu____17640 with
                 | (nbs',env2) ->
                     let b1 = norm_binder cfg env2 b  in
                     ((b1 :: nbs'), (dummy :: env2))) ([], env1) bs
           in
        match uu____17606 with | (nbs,uu____17720) -> FStar_List.rev nbs

and (norm_lcomp_opt :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env1  ->
      fun lopt  ->
        match lopt with
        | FStar_Pervasives_Native.Some rc ->
            let flags =
              filter_out_lcomp_cflags rc.FStar_Syntax_Syntax.residual_flags
               in
            let uu____17752 =
              let uu___2173_17753 = rc  in
              let uu____17754 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env1 [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2173_17753.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17754;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2173_17753.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17752
        | uu____17772 -> lopt

and (maybe_simplify :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun tm  ->
          let tm' = maybe_simplify_aux cfg env1 stack1 tm  in
          if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.b380
          then
            (let uu____17782 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17784 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17782 uu____17784)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_17796  ->
      match uu___15_17796 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17809 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17809 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17813 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____17813)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun tm  ->
          let tm1 =
            let uu____17821 = norm_cb cfg  in
            reduce_primops uu____17821 cfg env1 tm  in
          let uu____17826 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17826
          then tm1
          else
            (let w t =
               let uu___2202_17845 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2202_17845.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2202_17845.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17857 =
                 let uu____17858 = FStar_Syntax_Util.unmeta t  in
                 uu____17858.FStar_Syntax_Syntax.n  in
               match uu____17857 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17870 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17934)::args1,(bv,uu____17937)::bs1) ->
                   let uu____17991 =
                     let uu____17992 = FStar_Syntax_Subst.compress t  in
                     uu____17992.FStar_Syntax_Syntax.n  in
                   (match uu____17991 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17997 -> false)
               | ([],[]) -> true
               | (uu____18028,uu____18029) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18080 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18082 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18080
                    uu____18082)
               else ();
               (let uu____18087 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18087 with
                | (hd,args) ->
                    let uu____18126 =
                      let uu____18127 = FStar_Syntax_Subst.compress hd  in
                      uu____18127.FStar_Syntax_Syntax.n  in
                    (match uu____18126 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____18135 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18137 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18139 =
                               FStar_Syntax_Print.term_to_string hd  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18135 uu____18137 uu____18139)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18144 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18162 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18164 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18162
                    uu____18164)
               else ();
               (let uu____18169 = FStar_Syntax_Util.is_squash t  in
                match uu____18169 with
                | FStar_Pervasives_Native.Some (uu____18180,t') ->
                    is_applied bs t'
                | uu____18192 ->
                    let uu____18201 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18201 with
                     | FStar_Pervasives_Native.Some (uu____18212,t') ->
                         is_applied bs t'
                     | uu____18224 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18248 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18248 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18255)::(q,uu____18257)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18300 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18302 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18300 uu____18302)
                    else ();
                    (let uu____18307 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18307 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18312 =
                           let uu____18313 = FStar_Syntax_Subst.compress p
                              in
                           uu____18313.FStar_Syntax_Syntax.n  in
                         (match uu____18312 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18324 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18324))
                          | uu____18327 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18330)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18355 =
                           let uu____18356 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18356.FStar_Syntax_Syntax.n  in
                         (match uu____18355 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18367 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18367))
                          | uu____18370 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18374 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18374 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18379 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18379 with
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
                                     let uu____18393 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18393))
                               | uu____18396 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18401)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18426 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18426 with
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
                                     let uu____18440 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18440))
                               | uu____18443 -> FStar_Pervasives_Native.None)
                          | uu____18446 -> FStar_Pervasives_Native.None)
                     | uu____18449 -> FStar_Pervasives_Native.None))
               | uu____18452 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18465 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18465 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18471)::[],uu____18472,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18492 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18494 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18492
                         uu____18494)
                    else ();
                    is_quantified_const bv phi')
               | uu____18499 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18514 =
                 let uu____18515 = FStar_Syntax_Subst.compress phi  in
                 uu____18515.FStar_Syntax_Syntax.n  in
               match uu____18514 with
               | FStar_Syntax_Syntax.Tm_match (uu____18521,br::brs) ->
                   let uu____18588 = br  in
                   (match uu____18588 with
                    | (uu____18606,uu____18607,e) ->
                        let r =
                          let uu____18629 = simp_t e  in
                          match uu____18629 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18641 =
                                FStar_List.for_all
                                  (fun uu____18660  ->
                                     match uu____18660 with
                                     | (uu____18674,uu____18675,e') ->
                                         let uu____18689 = simp_t e'  in
                                         uu____18689 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18641
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18705 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18715 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18715
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18753 =
                 match uu____18753 with
                 | (t1,q) ->
                     let uu____18774 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18774 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18806 -> (t1, q))
                  in
               let uu____18819 = FStar_Syntax_Util.head_and_args t  in
               match uu____18819 with
               | (head,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18899 =
                 let uu____18900 = FStar_Syntax_Util.unmeta ty  in
                 uu____18900.FStar_Syntax_Syntax.n  in
               match uu____18899 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18905) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18910,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18934 -> false  in
             let simplify arg =
               let uu____18967 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18967, arg)  in
             let uu____18982 = is_forall_const tm1  in
             match uu____18982 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____18988 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18990 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18988
                       uu____18990)
                  else ();
                  (let uu____18995 = norm cfg env1 [] tm'  in
                   maybe_simplify_aux cfg env1 stack1 uu____18995))
             | FStar_Pervasives_Native.None  ->
                 let uu____18996 =
                   let uu____18997 = FStar_Syntax_Subst.compress tm1  in
                   uu____18997.FStar_Syntax_Syntax.n  in
                 (match uu____18996 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19001;
                              FStar_Syntax_Syntax.vars = uu____19002;_},uu____19003);
                         FStar_Syntax_Syntax.pos = uu____19004;
                         FStar_Syntax_Syntax.vars = uu____19005;_},args)
                      ->
                      let uu____19035 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19035
                      then
                        let uu____19038 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        (match uu____19038 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19096)::
                             (uu____19097,(arg,uu____19099))::[] ->
                             maybe_auto_squash arg
                         | (uu____19172,(arg,uu____19174))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19175)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19248)::uu____19249::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19319::(FStar_Pervasives_Native.Some (false
                                         ),uu____19320)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19390 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19408 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19408
                         then
                           let uu____19411 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify)
                              in
                           match uu____19411 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19469)::uu____19470::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19540::(FStar_Pervasives_Native.Some (true
                                           ),uu____19541)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19611)::(uu____19612,(arg,uu____19614))::[]
                               -> maybe_auto_squash arg
                           | (uu____19687,(arg,uu____19689))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19690)::[]
                               -> maybe_auto_squash arg
                           | uu____19763 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19781 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19781
                            then
                              let uu____19784 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify)
                                 in
                              match uu____19784 with
                              | uu____19842::(FStar_Pervasives_Native.Some
                                              (true ),uu____19843)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19913)::uu____19914::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19984)::(uu____19985,(arg,uu____19987))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20060,(p,uu____20062))::(uu____20063,
                                                                (q,uu____20065))::[]
                                  ->
                                  let uu____20137 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20137
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20142 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20160 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20160
                               then
                                 let uu____20163 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify)
                                    in
                                 match uu____20163 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20221)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20222)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20296)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20297)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20371)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20372)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20446)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20447)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20521,(arg,uu____20523))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20524)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20597)::(uu____20598,(arg,uu____20600))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20673,(arg,uu____20675))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20676)::[]
                                     ->
                                     let uu____20749 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20749
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20750)::(uu____20751,(arg,uu____20753))::[]
                                     ->
                                     let uu____20826 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20826
                                 | (uu____20827,(p,uu____20829))::(uu____20830,
                                                                   (q,uu____20832))::[]
                                     ->
                                     let uu____20904 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20904
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20909 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20927 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20927
                                  then
                                    let uu____20930 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify)
                                       in
                                    match uu____20930 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20988)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21032)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21076 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21094 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21094
                                     then
                                       match args with
                                       | (t,uu____21098)::[] ->
                                           let uu____21123 =
                                             let uu____21124 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21124.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21123 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21127::[],body,uu____21129)
                                                ->
                                                let uu____21164 = simp_t body
                                                   in
                                                (match uu____21164 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21170 -> tm1)
                                            | uu____21174 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21176))::(t,uu____21178)::[]
                                           ->
                                           let uu____21218 =
                                             let uu____21219 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21219.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21218 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21222::[],body,uu____21224)
                                                ->
                                                let uu____21259 = simp_t body
                                                   in
                                                (match uu____21259 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21267 -> tm1)
                                            | uu____21271 -> tm1)
                                       | uu____21272 -> tm1
                                     else
                                       (let uu____21285 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21285
                                        then
                                          match args with
                                          | (t,uu____21289)::[] ->
                                              let uu____21314 =
                                                let uu____21315 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21315.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21314 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21318::[],body,uu____21320)
                                                   ->
                                                   let uu____21355 =
                                                     simp_t body  in
                                                   (match uu____21355 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21361 -> tm1)
                                               | uu____21365 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21367))::(t,uu____21369)::[]
                                              ->
                                              let uu____21409 =
                                                let uu____21410 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21410.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21409 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21413::[],body,uu____21415)
                                                   ->
                                                   let uu____21450 =
                                                     simp_t body  in
                                                   (match uu____21450 with
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
                                                    | uu____21458 -> tm1)
                                               | uu____21462 -> tm1)
                                          | uu____21463 -> tm1
                                        else
                                          (let uu____21476 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21476
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21479;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21480;_},uu____21481)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21507;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21508;_},uu____21509)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21535 -> tm1
                                           else
                                             (let uu____21548 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____21548
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____21562 =
                                                    let uu____21563 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____21563.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____21562 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21574 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21588 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____21588
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____21627 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____21627
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21633 =
                                                         let uu____21634 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____21634.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____21633 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21637 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____21645 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____21645
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21654
                                                                  =
                                                                  let uu____21655
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____21655.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____21654
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,uu____21661)
                                                                    -> hd
                                                                | uu____21686
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____21690
                                                                =
                                                                let uu____21701
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____21701]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21690)
                                                       | uu____21734 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21739 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____21739 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21759 ->
                                                     let uu____21768 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____21768 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21774;
                         FStar_Syntax_Syntax.vars = uu____21775;_},args)
                      ->
                      let uu____21801 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21801
                      then
                        let uu____21804 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        (match uu____21804 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21862)::
                             (uu____21863,(arg,uu____21865))::[] ->
                             maybe_auto_squash arg
                         | (uu____21938,(arg,uu____21940))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21941)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22014)::uu____22015::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22085::(FStar_Pervasives_Native.Some (false
                                         ),uu____22086)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22156 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22174 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22174
                         then
                           let uu____22177 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify)
                              in
                           match uu____22177 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22235)::uu____22236::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22306::(FStar_Pervasives_Native.Some (true
                                           ),uu____22307)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22377)::(uu____22378,(arg,uu____22380))::[]
                               -> maybe_auto_squash arg
                           | (uu____22453,(arg,uu____22455))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22456)::[]
                               -> maybe_auto_squash arg
                           | uu____22529 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22547 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22547
                            then
                              let uu____22550 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify)
                                 in
                              match uu____22550 with
                              | uu____22608::(FStar_Pervasives_Native.Some
                                              (true ),uu____22609)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22679)::uu____22680::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22750)::(uu____22751,(arg,uu____22753))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22826,(p,uu____22828))::(uu____22829,
                                                                (q,uu____22831))::[]
                                  ->
                                  let uu____22903 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22903
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22908 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22926 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22926
                               then
                                 let uu____22929 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify)
                                    in
                                 match uu____22929 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22987)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22988)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23062)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23063)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23137)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23138)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23212)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23213)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23287,(arg,uu____23289))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23290)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23363)::(uu____23364,(arg,uu____23366))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23439,(arg,uu____23441))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23442)::[]
                                     ->
                                     let uu____23515 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23515
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23516)::(uu____23517,(arg,uu____23519))::[]
                                     ->
                                     let uu____23592 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23592
                                 | (uu____23593,(p,uu____23595))::(uu____23596,
                                                                   (q,uu____23598))::[]
                                     ->
                                     let uu____23670 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23670
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23675 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23693 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23693
                                  then
                                    let uu____23696 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify)
                                       in
                                    match uu____23696 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23754)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23798)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23842 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23860 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23860
                                     then
                                       match args with
                                       | (t,uu____23864)::[] ->
                                           let uu____23889 =
                                             let uu____23890 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23890.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23889 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23893::[],body,uu____23895)
                                                ->
                                                let uu____23930 = simp_t body
                                                   in
                                                (match uu____23930 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23936 -> tm1)
                                            | uu____23940 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23942))::(t,uu____23944)::[]
                                           ->
                                           let uu____23984 =
                                             let uu____23985 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23985.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23984 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23988::[],body,uu____23990)
                                                ->
                                                let uu____24025 = simp_t body
                                                   in
                                                (match uu____24025 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24033 -> tm1)
                                            | uu____24037 -> tm1)
                                       | uu____24038 -> tm1
                                     else
                                       (let uu____24051 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24051
                                        then
                                          match args with
                                          | (t,uu____24055)::[] ->
                                              let uu____24080 =
                                                let uu____24081 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24081.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24080 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24084::[],body,uu____24086)
                                                   ->
                                                   let uu____24121 =
                                                     simp_t body  in
                                                   (match uu____24121 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24127 -> tm1)
                                               | uu____24131 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24133))::(t,uu____24135)::[]
                                              ->
                                              let uu____24175 =
                                                let uu____24176 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24176.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24175 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24179::[],body,uu____24181)
                                                   ->
                                                   let uu____24216 =
                                                     simp_t body  in
                                                   (match uu____24216 with
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
                                                    | uu____24224 -> tm1)
                                               | uu____24228 -> tm1)
                                          | uu____24229 -> tm1
                                        else
                                          (let uu____24242 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24242
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24245;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24246;_},uu____24247)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24273;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24274;_},uu____24275)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24301 -> tm1
                                           else
                                             (let uu____24314 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____24314
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____24328 =
                                                    let uu____24329 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____24329.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____24328 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____24340 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24354 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____24354
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____24389 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____24389
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24395 =
                                                         let uu____24396 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____24396.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____24395 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24399 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24407 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24407
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24416
                                                                  =
                                                                  let uu____24417
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24417.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24416
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,uu____24423)
                                                                    -> hd
                                                                | uu____24448
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____24452
                                                                =
                                                                let uu____24463
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____24463]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24452)
                                                       | uu____24496 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24501 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____24501 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24521 ->
                                                     let uu____24530 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____24530 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24541 = simp_t t  in
                      (match uu____24541 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24550 ->
                      let uu____24573 = is_const_match tm1  in
                      (match uu____24573 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24582 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____24592  ->
               (let uu____24594 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24596 = FStar_Syntax_Print.term_to_string t  in
                let uu____24598 =
                  FStar_Util.string_of_int (FStar_List.length env1)  in
                let uu____24606 =
                  let uu____24608 =
                    let uu____24611 = firstn (Prims.of_int (4)) stack1  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24611
                     in
                  stack_to_string uu____24608  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24594 uu____24596 uu____24598 uu____24606);
               (let uu____24636 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24636
                then
                  let uu____24640 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24640 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24647 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24649 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24651 =
                          let uu____24653 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24653
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24647
                          uu____24649 uu____24651);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____24675 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack1 with
                | (Arg uu____24683)::uu____24684 -> true
                | uu____24694 -> false)
              in
           if uu____24675
           then
             let uu____24697 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____24697 (norm cfg env1 stack1)
           else
             (let t1 = maybe_simplify cfg env1 stack1 t  in
              match stack1 with
              | [] -> t1
              | (Debug (tm,time_then))::stack2 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____24711 =
                        let uu____24713 =
                          let uu____24715 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____24715  in
                        FStar_Util.string_of_int uu____24713  in
                      let uu____24722 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____24724 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                      let uu____24726 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____24711 uu____24722 uu____24724 uu____24726)
                   else ();
                   rebuild cfg env1 stack2 t1)
              | (Cfg cfg1)::stack2 -> rebuild cfg1 env1 stack2 t1
              | (Meta (uu____24735,m,r))::stack2 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env1 stack2 t2
              | (MemoLazy r)::stack2 ->
                  (set_memo cfg r (env1, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24764  ->
                        let uu____24765 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24765);
                   rebuild cfg env1 stack2 t1)
              | (Let (env',bs,lb,r))::stack2 ->
                  let body = FStar_Syntax_Subst.close bs t1  in
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body))
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env' stack2 t2
              | (Abs (env',bs,env'',lopt,r))::stack2 ->
                  let bs1 = norm_binders cfg env' bs  in
                  let lopt1 = norm_lcomp_opt cfg env'' lopt  in
                  let uu____24808 =
                    let uu___2831_24809 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2831_24809.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2831_24809.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env1 stack2 uu____24808
              | (Arg (Univ uu____24812,uu____24813,uu____24814))::uu____24815
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____24819,uu____24820))::uu____24821 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env1 stack2 t2
              | (Arg
                  (Clos (env_arg,tm,uu____24837,uu____24838),aq,r))::stack2
                  when
                  let uu____24890 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24890 ->
                  let t2 =
                    let uu____24894 =
                      let uu____24899 =
                        let uu____24900 = closure_as_term cfg env_arg tm  in
                        (uu____24900, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____24899  in
                    uu____24894 FStar_Pervasives_Native.None r  in
                  rebuild cfg env1 stack2 t2
              | (Arg (Clos (env_arg,tm,m,uu____24910),aq,r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24965  ->
                        let uu____24966 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____24966);
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
                        rebuild cfg env_arg stack2 t2
                      else
                        (let stack3 = (App (env1, t1, aq, r)) :: stack2  in
                         norm cfg env_arg stack3 tm))
                   else
                     (let uu____24986 = FStar_ST.op_Bang m  in
                      match uu____24986 with
                      | FStar_Pervasives_Native.None  ->
                          if
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          then
                            let arg = closure_as_term cfg env_arg tm  in
                            let t2 =
                              FStar_Syntax_Syntax.extend_app t1 (arg, aq)
                                FStar_Pervasives_Native.None r
                               in
                            rebuild cfg env_arg stack2 t2
                          else
                            (let stack3 = (MemoLazy m) ::
                               (App (env1, t1, aq, r)) :: stack2  in
                             norm cfg env_arg stack3 tm)
                      | FStar_Pervasives_Native.Some (uu____25074,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack2 t2))
              | (App (env2,head,aq,r))::stack' when should_reify cfg stack1
                  ->
                  let t0 = t1  in
                  let fallback msg uu____25130 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____25135  ->
                         let uu____25136 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____25136);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env2 stack' t2)
                     in
                  let uu____25146 =
                    let uu____25147 = FStar_Syntax_Subst.compress t1  in
                    uu____25147.FStar_Syntax_Syntax.n  in
                  (match uu____25146 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env2 stack1 t2
                         m ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____25175 = closure_as_term cfg env2 ty  in
                         reify_lift cfg t2 msrc mtgt uu____25175  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____25179  ->
                             let uu____25180 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____25180);
                        (let uu____25183 = FStar_List.tl stack1  in
                         norm cfg env2 uu____25183 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____25184);
                          FStar_Syntax_Syntax.pos = uu____25185;
                          FStar_Syntax_Syntax.vars = uu____25186;_},(e,uu____25188)::[])
                       -> norm cfg env2 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____25227 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____25244 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____25244 with
                        | (hd,args) ->
                            let uu____25287 =
                              let uu____25288 = FStar_Syntax_Util.un_uinst hd
                                 in
                              uu____25288.FStar_Syntax_Syntax.n  in
                            (match uu____25287 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____25292 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____25292 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____25295;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____25296;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____25297;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____25299;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____25300;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____25301;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____25302;_}
                                      when (FStar_List.length args) = n ->
                                      norm cfg env2 stack' t1
                                  | uu____25338 -> fallback " (3)" ())
                             | uu____25342 -> fallback " (4)" ()))
                   | uu____25344 -> fallback " (2)" ())
              | (App (env2,head,aq,r))::stack2 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env2 stack2 t2
              | (CBVApp (env',head,aq,r))::stack2 ->
                  let uu____25367 =
                    let uu____25368 =
                      let uu____25369 =
                        let uu____25376 =
                          let uu____25377 =
                            let uu____25409 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env1, t1, uu____25409, false)  in
                          Clos uu____25377  in
                        (uu____25376, aq, (t1.FStar_Syntax_Syntax.pos))  in
                      Arg uu____25369  in
                    uu____25368 :: stack2  in
                  norm cfg env' uu____25367 head
              | (Match (env',branches1,cfg1,r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____25484  ->
                        let uu____25485 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____25485);
                   (let scrutinee_env = env1  in
                    let env2 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____25496 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25501  ->
                           let uu____25502 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____25504 =
                             let uu____25506 =
                               FStar_All.pipe_right branches1
                                 (FStar_List.map
                                    (fun uu____25536  ->
                                       match uu____25536 with
                                       | (p,uu____25547,uu____25548) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____25506
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____25502 uu____25504);
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
                                   (fun uu___16_25573  ->
                                      match uu___16_25573 with
                                      | FStar_TypeChecker_Env.InliningDelta 
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                           -> true
                                      | uu____25577 -> false))
                               in
                            let steps =
                              let uu___3008_25580 =
                                cfg1.FStar_TypeChecker_Cfg.steps  in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3008_25580.FStar_TypeChecker_Cfg.for_extraction)
                              }  in
                            let uu___3011_25587 = cfg1  in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3011_25587.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3011_25587.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3011_25587.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3011_25587.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3011_25587.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3011_25587.FStar_TypeChecker_Cfg.reifying)
                            })
                          in
                       let norm_or_whnf env3 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env3 t2
                         else norm cfg_exclude_zeta env3 [] t2  in
                       let rec norm_pat env3 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____25662 ->
                             (p, env3)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____25693 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25782  ->
                                       fun uu____25783  ->
                                         match (uu____25782, uu____25783)
                                         with
                                         | ((pats1,env4),(p1,b)) ->
                                             let uu____25933 =
                                               norm_pat env4 p1  in
                                             (match uu____25933 with
                                              | (p2,env5) ->
                                                  (((p2, b) :: pats1), env5)))
                                    ([], env3))
                                in
                             (match uu____25693 with
                              | (pats1,env4) ->
                                  ((let uu___3039_26103 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3039_26103.FStar_Syntax_Syntax.p)
                                    }), env4))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3043_26124 = x  in
                               let uu____26125 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3043_26124.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3043_26124.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26125
                               }  in
                             ((let uu___3046_26139 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3046_26139.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3050_26150 = x  in
                               let uu____26151 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3050_26150.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3050_26150.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26151
                               }  in
                             ((let uu___3053_26165 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3053_26165.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3059_26181 = x  in
                               let uu____26182 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3059_26181.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3059_26181.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26182
                               }  in
                             let t3 = norm_or_whnf env3 t2  in
                             ((let uu___3063_26197 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3063_26197.FStar_Syntax_Syntax.p)
                               }), env3)
                          in
                       let branches2 =
                         match env2 with
                         | [] when whnf -> branches1
                         | uu____26241 ->
                             FStar_All.pipe_right branches1
                               (FStar_List.map
                                  (fun branch  ->
                                     let uu____26271 =
                                       FStar_Syntax_Subst.open_branch branch
                                        in
                                     match uu____26271 with
                                     | (p,wopt,e) ->
                                         let uu____26291 = norm_pat env2 p
                                            in
                                         (match uu____26291 with
                                          | (p1,env3) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____26346 =
                                                      norm_or_whnf env3 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____26346
                                                 in
                                              let e1 = norm_or_whnf env3 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____26363 =
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
                         if uu____26363
                         then
                           norm
                             (let uu___3082_26370 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3084_26373 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.zeta_full =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.zeta_full);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3084_26373.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3082_26370.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3082_26370.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3082_26370.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3082_26370.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3082_26370.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3082_26370.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3082_26370.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3082_26370.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____26377 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches2)) r
                          in
                       rebuild cfg1 env2 stack2 uu____26377)
                       in
                    let rec is_cons head =
                      let uu____26403 =
                        let uu____26404 = FStar_Syntax_Subst.compress head
                           in
                        uu____26404.FStar_Syntax_Syntax.n  in
                      match uu____26403 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____26409) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____26414 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26416;
                            FStar_Syntax_Syntax.fv_delta = uu____26417;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26419;
                            FStar_Syntax_Syntax.fv_delta = uu____26420;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____26421);_}
                          -> true
                      | uu____26429 -> false  in
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
                      let uu____26598 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____26598 with
                      | (head,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____26695 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26737 ->
                                    let uu____26738 =
                                      let uu____26740 = is_cons head  in
                                      Prims.op_Negation uu____26740  in
                                    FStar_Util.Inr uu____26738)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____26769 =
                                 let uu____26770 =
                                   FStar_Syntax_Util.un_uinst head  in
                                 uu____26770.FStar_Syntax_Syntax.n  in
                               (match uu____26769 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26789 ->
                                    let uu____26790 =
                                      let uu____26792 = is_cons head  in
                                      Prims.op_Negation uu____26792  in
                                    FStar_Util.Inr uu____26790))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____26883)::rest_a,(p1,uu____26886)::rest_p)
                          ->
                          let uu____26945 = matches_pat t2 p1  in
                          (match uu____26945 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____26998 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____27121 = matches_pat scrutinee1 p1  in
                          (match uu____27121 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____27167  ->
                                     let uu____27168 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____27170 =
                                       let uu____27172 =
                                         FStar_List.map
                                           (fun uu____27184  ->
                                              match uu____27184 with
                                              | (uu____27190,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____27172
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____27168 uu____27170);
                                (let env0 = env2  in
                                 let env3 =
                                   FStar_List.fold_left
                                     (fun env3  ->
                                        fun uu____27226  ->
                                          match uu____27226 with
                                          | (bv,t2) ->
                                              let uu____27249 =
                                                let uu____27256 =
                                                  let uu____27259 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____27259
                                                   in
                                                let uu____27260 =
                                                  let uu____27261 =
                                                    let uu____27293 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____27293,
                                                      false)
                                                     in
                                                  Clos uu____27261  in
                                                (uu____27256, uu____27260)
                                                 in
                                              uu____27249 :: env3) env2 s
                                    in
                                 let uu____27386 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env3 stack2 uu____27386)))
                       in
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
  fun ps  ->
    fun s  ->
      fun e  ->
        fun t  ->
          let c = FStar_TypeChecker_Cfg.config' ps s e  in
          FStar_TypeChecker_Cfg.log_cfg c
            (fun uu____27419  ->
               let uu____27420 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____27420);
          (let uu____27423 = is_nbe_request s  in
           if uu____27423
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27429  ->
                   let uu____27430 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27430);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27436  ->
                   let uu____27437 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27437);
              (let uu____27440 =
                 FStar_Util.record_time (fun uu____27447  -> nbe_eval c s t)
                  in
               match uu____27440 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27456  ->
                         let uu____27457 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27459 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27457 uu____27459);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27467  ->
                   let uu____27468 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27468);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27474  ->
                   let uu____27475 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27475);
              (let uu____27478 =
                 FStar_Util.record_time (fun uu____27485  -> norm c [] [] t)
                  in
               match uu____27478 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27500  ->
                         let uu____27501 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27503 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27501 uu____27503);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27522 =
          let uu____27526 =
            let uu____27528 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____27528  in
          FStar_Pervasives_Native.Some uu____27526  in
        FStar_Profiling.profile
          (fun uu____27531  -> normalize_with_primitive_steps [] s e t)
          uu____27522 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____27553  ->
             let uu____27554 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27554);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27560  ->
             let uu____27561 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27561);
        (let uu____27564 =
           FStar_Util.record_time (fun uu____27571  -> norm_comp cfg [] c)
            in
         match uu____27564 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27586  ->
                   let uu____27587 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____27589 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27587
                     uu____27589);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env1  ->
    fun u  ->
      let uu____27603 = FStar_TypeChecker_Cfg.config [] env1  in
      norm_universe uu____27603 [] u
  
let (non_info_norm :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env1  ->
    fun t  ->
      let steps =
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant;
        FStar_TypeChecker_Env.AllowUnboundUniverses;
        FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.HNF;
        FStar_TypeChecker_Env.Unascribe;
        FStar_TypeChecker_Env.ForExtraction]  in
      let uu____27625 = normalize steps env1 t  in
      FStar_TypeChecker_Env.non_informative env1 uu____27625
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env1  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27637 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env1 t ->
          let uu___3252_27656 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3252_27656.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3252_27656.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env1
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27663 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env1 ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27663
          then
            let ct1 =
              let uu____27667 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27667 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____27674 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27674
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3262_27681 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3262_27681.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3262_27681.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3262_27681.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env1 c
                     in
                  let uu___3266_27683 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3266_27683.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3266_27683.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3266_27683.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3266_27683.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3269_27684 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3269_27684.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3269_27684.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27687 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env1  ->
    fun lc  ->
      let uu____27699 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env1 lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____27699
      then
        let uu____27702 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____27702 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3277_27706 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env1)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3277_27706.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3277_27706.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3277_27706.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env1  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3284_27725  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                   t) ()
        with
        | uu___3283_27728 ->
            ((let uu____27730 =
                let uu____27736 =
                  let uu____27738 = FStar_Util.message_of_exn uu___3283_27728
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27738
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27736)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27730);
             t)
         in
      FStar_Syntax_Print.term_to_string' env1.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env1  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3294_27757  ->
             match () with
             | () ->
                 let uu____27758 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                    in
                 norm_comp uu____27758 [] c) ()
        with
        | uu___3293_27767 ->
            ((let uu____27769 =
                let uu____27775 =
                  let uu____27777 = FStar_Util.message_of_exn uu___3293_27767
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27777
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27775)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27769);
             c)
         in
      FStar_Syntax_Print.comp_to_string' env1.FStar_TypeChecker_Env.dsenv c1
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun steps  ->
    fun env1  ->
      fun t0  ->
        let t =
          normalize (FStar_List.append steps [FStar_TypeChecker_Env.Beta])
            env1 t0
           in
        let rec aux t1 =
          let t2 = FStar_Syntax_Subst.compress t1  in
          match t2.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              let t01 = aux x.FStar_Syntax_Syntax.sort  in
              (match t01.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_refine (y,phi1) ->
                   let uu____27826 =
                     let uu____27827 =
                       let uu____27834 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27834)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27827  in
                   mk uu____27826 t01.FStar_Syntax_Syntax.pos
               | uu____27839 -> t2)
          | uu____27840 -> t2  in
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
    fun env1  ->
      fun t  -> normalize (FStar_List.append steps whnf_steps) env1 t
  
let (unfold_whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env1  -> fun t  -> unfold_whnf' [] env1 t 
let (reduce_or_remove_uvar_solutions :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun remove  ->
    fun env1  ->
      fun t  ->
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
  = fun env1  -> fun t  -> reduce_or_remove_uvar_solutions false env1 t 
let (remove_uvar_solutions :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun env1  -> fun t  -> reduce_or_remove_uvar_solutions true env1 t 
let (eta_expand_with_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun e  ->
      fun t_e  ->
        let uu____27934 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27934 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27947 ->
                 let uu____27948 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27948 with
                  | (actuals,uu____27958,uu____27959) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27979 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27979 with
                         | (binders,args) ->
                             let uu____27990 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27990
                               (FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.residual_comp_of_comp c)))))
  
let (eta_expand :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x ->
          eta_expand_with_type env1 t x.FStar_Syntax_Syntax.sort
      | uu____28005 ->
          let uu____28006 = FStar_Syntax_Util.head_and_args t  in
          (match uu____28006 with
           | (head,args) ->
               let uu____28049 =
                 let uu____28050 = FStar_Syntax_Subst.compress head  in
                 uu____28050.FStar_Syntax_Syntax.n  in
               (match uu____28049 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____28071 =
                      let uu____28078 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____28078  in
                    (match uu____28071 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____28102 =
                              env1.FStar_TypeChecker_Env.type_of
                                (let uu___3364_28110 = env1  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3364_28110.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3364_28110.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3364_28110.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3364_28110.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3364_28110.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3364_28110.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3364_28110.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3364_28110.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3364_28110.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3364_28110.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3364_28110.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3364_28110.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3364_28110.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3364_28110.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3364_28110.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3364_28110.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3364_28110.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3364_28110.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3364_28110.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3364_28110.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3364_28110.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3364_28110.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3364_28110.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3364_28110.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3364_28110.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3364_28110.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3364_28110.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3364_28110.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3364_28110.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3364_28110.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3364_28110.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3364_28110.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3364_28110.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3364_28110.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3364_28110.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3364_28110.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3364_28110.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3364_28110.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3364_28110.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3364_28110.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3364_28110.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3364_28110.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3364_28110.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____28102 with
                            | (uu____28113,ty,uu____28115) ->
                                eta_expand_with_type env1 t ty))
                | uu____28116 ->
                    let uu____28117 =
                      env1.FStar_TypeChecker_Env.type_of
                        (let uu___3371_28125 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3371_28125.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3371_28125.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3371_28125.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3371_28125.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3371_28125.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3371_28125.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3371_28125.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3371_28125.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3371_28125.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3371_28125.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3371_28125.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3371_28125.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3371_28125.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3371_28125.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3371_28125.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3371_28125.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3371_28125.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3371_28125.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3371_28125.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3371_28125.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3371_28125.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3371_28125.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3371_28125.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3371_28125.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3371_28125.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3371_28125.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3371_28125.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3371_28125.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3371_28125.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3371_28125.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3371_28125.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3371_28125.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3371_28125.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3371_28125.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3371_28125.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3371_28125.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3371_28125.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3371_28125.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3371_28125.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3371_28125.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3371_28125.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3371_28125.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3371_28125.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____28117 with
                     | (uu____28128,ty,uu____28130) ->
                         eta_expand_with_type env1 t ty)))
  
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let mk1 x =
      FStar_Syntax_Syntax.mk x FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
       in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___3383_28212 = x  in
      let uu____28213 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3383_28212.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3383_28212.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28213
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28216 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28232 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28233 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28234 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28235 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28242 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28243 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28244 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3409_28278 = rc  in
          let uu____28279 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28288 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3409_28278.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28279;
            FStar_Syntax_Syntax.residual_flags = uu____28288
          }  in
        let uu____28291 =
          let uu____28292 =
            let uu____28311 = elim_delayed_subst_binders bs  in
            let uu____28320 = elim_delayed_subst_term t2  in
            let uu____28323 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28311, uu____28320, uu____28323)  in
          FStar_Syntax_Syntax.Tm_abs uu____28292  in
        mk1 uu____28291
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28360 =
          let uu____28361 =
            let uu____28376 = elim_delayed_subst_binders bs  in
            let uu____28385 = elim_delayed_subst_comp c  in
            (uu____28376, uu____28385)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28361  in
        mk1 uu____28360
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28404 =
          let uu____28405 =
            let uu____28412 = elim_bv bv  in
            let uu____28413 = elim_delayed_subst_term phi  in
            (uu____28412, uu____28413)  in
          FStar_Syntax_Syntax.Tm_refine uu____28405  in
        mk1 uu____28404
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28444 =
          let uu____28445 =
            let uu____28462 = elim_delayed_subst_term t2  in
            let uu____28465 = elim_delayed_subst_args args  in
            (uu____28462, uu____28465)  in
          FStar_Syntax_Syntax.Tm_app uu____28445  in
        mk1 uu____28444
    | FStar_Syntax_Syntax.Tm_match (t2,branches1) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3431_28537 = p  in
              let uu____28538 =
                let uu____28539 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28539  in
              {
                FStar_Syntax_Syntax.v = uu____28538;
                FStar_Syntax_Syntax.p =
                  (uu___3431_28537.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3435_28541 = p  in
              let uu____28542 =
                let uu____28543 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28543  in
              {
                FStar_Syntax_Syntax.v = uu____28542;
                FStar_Syntax_Syntax.p =
                  (uu___3435_28541.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3441_28550 = p  in
              let uu____28551 =
                let uu____28552 =
                  let uu____28559 = elim_bv x  in
                  let uu____28560 = elim_delayed_subst_term t0  in
                  (uu____28559, uu____28560)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28552  in
              {
                FStar_Syntax_Syntax.v = uu____28551;
                FStar_Syntax_Syntax.p =
                  (uu___3441_28550.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3447_28585 = p  in
              let uu____28586 =
                let uu____28587 =
                  let uu____28601 =
                    FStar_List.map
                      (fun uu____28627  ->
                         match uu____28627 with
                         | (x,b) ->
                             let uu____28644 = elim_pat x  in
                             (uu____28644, b)) pats
                     in
                  (fv, uu____28601)  in
                FStar_Syntax_Syntax.Pat_cons uu____28587  in
              {
                FStar_Syntax_Syntax.v = uu____28586;
                FStar_Syntax_Syntax.p =
                  (uu___3447_28585.FStar_Syntax_Syntax.p)
              }
          | uu____28659 -> p  in
        let elim_branch uu____28683 =
          match uu____28683 with
          | (pat,wopt,t3) ->
              let uu____28709 = elim_pat pat  in
              let uu____28712 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28715 = elim_delayed_subst_term t3  in
              (uu____28709, uu____28712, uu____28715)
           in
        let uu____28720 =
          let uu____28721 =
            let uu____28744 = elim_delayed_subst_term t2  in
            let uu____28747 = FStar_List.map elim_branch branches1  in
            (uu____28744, uu____28747)  in
          FStar_Syntax_Syntax.Tm_match uu____28721  in
        mk1 uu____28720
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28878 =
          match uu____28878 with
          | (tc,topt) ->
              let uu____28913 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28923 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28923
                | FStar_Util.Inr c ->
                    let uu____28925 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28925
                 in
              let uu____28926 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28913, uu____28926)
           in
        let uu____28935 =
          let uu____28936 =
            let uu____28963 = elim_delayed_subst_term t2  in
            let uu____28966 = elim_ascription a  in
            (uu____28963, uu____28966, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28936  in
        mk1 uu____28935
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3477_29029 = lb  in
          let uu____29030 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____29033 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3477_29029.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3477_29029.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____29030;
            FStar_Syntax_Syntax.lbeff =
              (uu___3477_29029.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____29033;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3477_29029.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3477_29029.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____29036 =
          let uu____29037 =
            let uu____29051 =
              let uu____29059 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____29059)  in
            let uu____29071 = elim_delayed_subst_term t2  in
            (uu____29051, uu____29071)  in
          FStar_Syntax_Syntax.Tm_let uu____29037  in
        mk1 uu____29036
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____29116 =
          let uu____29117 =
            let uu____29124 = elim_delayed_subst_term tm  in
            (uu____29124, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____29117  in
        mk1 uu____29116
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29135 =
          let uu____29136 =
            let uu____29143 = elim_delayed_subst_term t2  in
            let uu____29146 = elim_delayed_subst_meta md  in
            (uu____29143, uu____29146)  in
          FStar_Syntax_Syntax.Tm_meta uu____29136  in
        mk1 uu____29135

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29155  ->
         match uu___17_29155 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29159 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29159
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
        let uu____29182 =
          let uu____29183 =
            let uu____29192 = elim_delayed_subst_term t  in
            (uu____29192, uopt)  in
          FStar_Syntax_Syntax.Total uu____29183  in
        mk1 uu____29182
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29209 =
          let uu____29210 =
            let uu____29219 = elim_delayed_subst_term t  in
            (uu____29219, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29210  in
        mk1 uu____29209
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3510_29228 = ct  in
          let uu____29229 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29232 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29243 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3510_29228.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3510_29228.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29229;
            FStar_Syntax_Syntax.effect_args = uu____29232;
            FStar_Syntax_Syntax.flags = uu____29243
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29246  ->
    match uu___18_29246 with
    | FStar_Syntax_Syntax.Meta_pattern (names,args) ->
        let uu____29281 =
          let uu____29302 = FStar_List.map elim_delayed_subst_term names  in
          let uu____29311 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29302, uu____29311)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29281
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____29366 =
          let uu____29373 = elim_delayed_subst_term t  in (m, uu____29373)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____29366
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____29385 =
          let uu____29394 = elim_delayed_subst_term t  in
          (m1, m2, uu____29394)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29385
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
      (fun uu____29427  ->
         match uu____29427 with
         | (t,q) ->
             let uu____29446 = elim_delayed_subst_term t  in (uu____29446, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29474  ->
         match uu____29474 with
         | (x,q) ->
             let uu____29493 =
               let uu___3536_29494 = x  in
               let uu____29495 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3536_29494.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3536_29494.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29495
               }  in
             (uu____29493, q)) bs

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
  fun env1  ->
    fun univ_names  ->
      fun binders  ->
        fun tc  ->
          let t =
            match (binders, tc) with
            | ([],FStar_Util.Inl t) -> t
            | ([],FStar_Util.Inr c) ->
                failwith "Impossible: empty bindes with a comp"
            | (uu____29603,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29635,FStar_Util.Inl t) ->
                let uu____29657 =
                  let uu____29664 =
                    let uu____29665 =
                      let uu____29680 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29680)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29665  in
                  FStar_Syntax_Syntax.mk uu____29664  in
                uu____29657 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29693 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29693 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env1 t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29725 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29798 ->
                    let uu____29799 =
                      let uu____29808 =
                        let uu____29809 = FStar_Syntax_Subst.compress t4  in
                        uu____29809.FStar_Syntax_Syntax.n  in
                      (uu____29808, tc)  in
                    (match uu____29799 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29838) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29885) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29930,FStar_Util.Inl uu____29931) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29962 -> failwith "Impossible")
                 in
              (match uu____29725 with
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
  fun env1  ->
    fun univ_names  ->
      fun binders  ->
        fun t  ->
          let uu____30101 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inl t)  in
          match uu____30101 with
          | (univ_names1,binders1,tc) ->
              let uu____30175 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30175)
  
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
  fun env1  ->
    fun univ_names  ->
      fun binders  ->
        fun c  ->
          let uu____30229 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inr c)  in
          match uu____30229 with
          | (univ_names1,binders1,tc) ->
              let uu____30303 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30303)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env1  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____30345 = elim_uvars_aux_t env1 univ_names binders typ  in
          (match uu____30345 with
           | (univ_names1,binders1,typ1) ->
               let uu___3619_30385 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3619_30385.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3619_30385.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3619_30385.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3619_30385.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3619_30385.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3625_30400 = s  in
          let uu____30401 =
            let uu____30402 =
              let uu____30411 = FStar_List.map (elim_uvars env1) sigs  in
              (uu____30411, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____30402  in
          {
            FStar_Syntax_Syntax.sigel = uu____30401;
            FStar_Syntax_Syntax.sigrng =
              (uu___3625_30400.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3625_30400.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3625_30400.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3625_30400.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3625_30400.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____30430 = elim_uvars_aux_t env1 univ_names [] typ  in
          (match uu____30430 with
           | (univ_names1,uu____30454,typ1) ->
               let uu___3639_30476 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3639_30476.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3639_30476.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3639_30476.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3639_30476.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3639_30476.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____30483 = elim_uvars_aux_t env1 univ_names [] typ  in
          (match uu____30483 with
           | (univ_names1,uu____30507,typ1) ->
               let uu___3650_30529 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3650_30529.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3650_30529.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3650_30529.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3650_30529.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3650_30529.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30559 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30559 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____30584 =
                            let uu____30585 =
                              let uu____30586 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env1 uu____30586  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30585
                             in
                          elim_delayed_subst_term uu____30584  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3666_30589 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3666_30589.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3666_30589.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3666_30589.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3666_30589.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3669_30590 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3669_30590.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3669_30590.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3669_30590.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3669_30590.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3669_30590.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3673_30597 = s  in
          let uu____30598 =
            let uu____30599 = remove_uvar_solutions env1 t  in
            FStar_Syntax_Syntax.Sig_main uu____30599  in
          {
            FStar_Syntax_Syntax.sigel = uu____30598;
            FStar_Syntax_Syntax.sigrng =
              (uu___3673_30597.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3673_30597.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3673_30597.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3673_30597.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3673_30597.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____30603 = elim_uvars_aux_t env1 us [] t  in
          (match uu____30603 with
           | (us1,uu____30627,t1) ->
               let uu___3684_30649 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3684_30649.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3684_30649.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3684_30649.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3684_30649.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3684_30649.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30651 =
            elim_uvars_aux_t env1 ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____30651 with
           | (univs,binders,uu____30670) ->
               let uu____30691 =
                 let uu____30696 = FStar_Syntax_Subst.univ_var_opening univs
                    in
                 match uu____30696 with
                 | (univs_opening,univs1) ->
                     let uu____30719 =
                       FStar_Syntax_Subst.univ_var_closing univs1  in
                     (univs_opening, uu____30719)
                  in
               (match uu____30691 with
                | (univs_opening,univs_closing) ->
                    let uu____30722 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30728 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30729 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30728, uu____30729)  in
                    (match uu____30722 with
                     | (b_opening,b_closing) ->
                         let n = FStar_List.length univs  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30755 =
                           match uu____30755 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30773 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30773 with
                                | (us1,t1) ->
                                    let uu____30784 =
                                      let uu____30793 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30798 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30793, uu____30798)  in
                                    (match uu____30784 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30821 =
                                           let uu____30830 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____30835 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____30830, uu____30835)  in
                                         (match uu____30821 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30859 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30859
                                                 in
                                              let uu____30860 =
                                                elim_uvars_aux_t env1 [] []
                                                  t2
                                                 in
                                              (match uu____30860 with
                                               | (uu____30887,uu____30888,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30911 =
                                                       let uu____30912 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30912
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30911
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30921 =
                             elim_uvars_aux_t env1 univs binders t  in
                           match uu____30921 with
                           | (uu____30940,uu____30941,t1) -> t1  in
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
                             | uu____31017 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____31044 =
                               let uu____31045 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____31045.FStar_Syntax_Syntax.n  in
                             match uu____31044 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____31104 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31138 =
                               let uu____31139 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31139.FStar_Syntax_Syntax.n  in
                             match uu____31138 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31162) ->
                                 let uu____31187 = destruct_action_body body
                                    in
                                 (match uu____31187 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31236 ->
                                 let uu____31237 = destruct_action_body t  in
                                 (match uu____31237 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31292 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31292 with
                           | (action_univs,t) ->
                               let uu____31301 = destruct_action_typ_templ t
                                  in
                               (match uu____31301 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3768_31348 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3768_31348.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3768_31348.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3771_31350 = ed  in
                           let uu____31351 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____31352 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____31353 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3771_31350.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3771_31350.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31351;
                             FStar_Syntax_Syntax.combinators = uu____31352;
                             FStar_Syntax_Syntax.actions = uu____31353;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3771_31350.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3774_31356 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3774_31356.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3774_31356.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3774_31356.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3774_31356.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3774_31356.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31377 =
            match uu___19_31377 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____31408 = elim_uvars_aux_t env1 us [] t  in
                (match uu____31408 with
                 | (us1,uu____31440,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3789_31471 = sub_eff  in
            let uu____31472 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____31475 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3789_31471.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3789_31471.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31472;
              FStar_Syntax_Syntax.lift = uu____31475
            }  in
          let uu___3792_31478 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3792_31478.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3792_31478.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3792_31478.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3792_31478.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3792_31478.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____31488 = elim_uvars_aux_c env1 univ_names binders comp  in
          (match uu____31488 with
           | (univ_names1,binders1,comp1) ->
               let uu___3805_31528 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3805_31528.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3805_31528.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3805_31528.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3805_31528.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3805_31528.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31531 -> s
      | FStar_Syntax_Syntax.Sig_fail uu____31532 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31545 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n,p,(us_t,t),(us_ty,ty))
          ->
          let uu____31575 = elim_uvars_aux_t env1 us_t [] t  in
          (match uu____31575 with
           | (us_t1,uu____31599,t1) ->
               let uu____31621 = elim_uvars_aux_t env1 us_ty [] ty  in
               (match uu____31621 with
                | (us_ty1,uu____31645,ty1) ->
                    let uu___3832_31667 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3832_31667.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3832_31667.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3832_31667.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3832_31667.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3832_31667.FStar_Syntax_Syntax.sigopts)
                    }))
  
let (erase_universes :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env1  ->
    fun t  ->
      normalize
        [FStar_TypeChecker_Env.EraseUniverses;
        FStar_TypeChecker_Env.AllowUnboundUniverses] env1 t
  
let (unfold_head_once :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env1  ->
    fun t  ->
      let aux f us args =
        let uu____31718 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env1 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____31718 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____31740 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____31740 with
             | (uu____31747,head_def) ->
                 let t' =
                   FStar_Syntax_Syntax.mk_Tm_app head_def args
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                    in
                 let t'1 =
                   normalize
                     [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota]
                     env1 t'
                    in
                 FStar_Pervasives_Native.Some t'1)
         in
      let uu____31753 = FStar_Syntax_Util.head_and_args t  in
      match uu____31753 with
      | (head,args) ->
          let uu____31798 =
            let uu____31799 = FStar_Syntax_Subst.compress head  in
            uu____31799.FStar_Syntax_Syntax.n  in
          (match uu____31798 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31806;
                  FStar_Syntax_Syntax.vars = uu____31807;_},us)
               -> aux fv us args
           | uu____31813 -> FStar_Pervasives_Native.None)
  