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
          | FStar_Syntax_Syntax.U_unif uu____1702 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1713 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1720 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1720 norm_univs_for_max  in
              (match us1 with
               | u_k::hd::rest ->
                   let rest1 = hd :: rest  in
                   let uu____1737 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1737 with
                    | (FStar_Syntax_Syntax.U_zero ,n) ->
                        let uu____1748 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1758 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1758 with
                                  | (uu____1765,m) -> n <= m))
                           in
                        if uu____1748 then rest1 else us1
                    | uu____1774 -> us1)
               | uu____1780 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1784 = aux u3  in
              FStar_List.map
                (fun uu____1787  -> FStar_Syntax_Syntax.U_succ uu____1787)
                uu____1784
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1791 = aux u  in
           match uu____1791 with
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
            (fun uu____1952  ->
               let uu____1953 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1955 = env_to_string env1  in
               let uu____1957 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 ">>> %s (env=%s)\nClosure_as_term %s\n"
                 uu____1953 uu____1955 uu____1957);
          (match env1 with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env1 stack1 t
           | uu____1970 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1973 ->
                    let uu____1988 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env1 stack1 uu____1988
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_constant uu____1989 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_name uu____1990 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_lazy uu____1991 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_fvar uu____1992 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____2017 ->
                           let uu____2030 =
                             let uu____2032 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____2034 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____2032 uu____2034
                              in
                           failwith uu____2030
                       | uu____2039 -> inline_closure_env cfg env1 stack1 t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_2075  ->
                                         match uu___4_2075 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____2082 =
                                               let uu____2089 =
                                                 inline_closure_env cfg env1
                                                   [] t1
                                                  in
                                               (x, uu____2089)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____2082
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___249_2101 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___249_2101.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___249_2101.FStar_Syntax_Syntax.sort)
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
                                              | uu____2107 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____2110 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___258_2115 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___258_2115.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___258_2115.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____2136 =
                        let uu____2137 = norm_universe cfg env1 u  in
                        FStar_Syntax_Syntax.Tm_type uu____2137  in
                      mk uu____2136 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____2145 =
                        FStar_List.map (norm_universe cfg env1) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2145  in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____2147 = lookup_bvar env1 x  in
                    (match uu____2147 with
                     | Univ uu____2150 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___274_2155 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___274_2155.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___274_2155.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env1 stack1 t1
                     | Clos (env2,t0,uu____2161,uu____2162) ->
                         inline_closure_env cfg env2 stack1 t0)
                | FStar_Syntax_Syntax.Tm_app (head,args) ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____2253  ->
                              fun stack2  ->
                                match uu____2253 with
                                | (a,aq) ->
                                    let uu____2265 =
                                      let uu____2266 =
                                        let uu____2273 =
                                          let uu____2274 =
                                            let uu____2306 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env1, a, uu____2306, false)  in
                                          Clos uu____2274  in
                                        (uu____2273, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2266  in
                                    uu____2265 :: stack2) args)
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
                    let uu____2474 = close_binders cfg env1 bs  in
                    (match uu____2474 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____2524) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env1 stack1
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2535 =
                      let uu____2548 =
                        let uu____2557 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2557]  in
                      close_binders cfg env1 uu____2548  in
                    (match uu____2535 with
                     | (x1,env2) ->
                         let phi1 = non_tail_inline_closure_env cfg env2 phi
                            in
                         let t1 =
                           let uu____2602 =
                             let uu____2603 =
                               let uu____2610 =
                                 let uu____2611 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2611
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2610, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2603  in
                           mk uu____2602 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env2 stack1 t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2710 =
                            non_tail_inline_closure_env cfg env1 t2  in
                          FStar_Util.Inl uu____2710
                      | FStar_Util.Inr c ->
                          let uu____2724 = close_comp cfg env1 c  in
                          FStar_Util.Inr uu____2724
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env1)
                       in
                    let t2 =
                      let uu____2743 =
                        let uu____2744 =
                          let uu____2771 =
                            non_tail_inline_closure_env cfg env1 t1  in
                          (uu____2771, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2744  in
                      mk uu____2743 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env1 stack1 t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2817 =
                            let uu____2818 =
                              let uu____2825 =
                                non_tail_inline_closure_env cfg env1 t'  in
                              (uu____2825, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2818  in
                          mk uu____2817 t.FStar_Syntax_Syntax.pos
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
                        (fun env2  -> fun uu____2880  -> dummy :: env2) env1
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
                    let uu____2901 =
                      let uu____2912 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2912
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2934 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___366_2950 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___366_2950.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___366_2950.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2934))
                       in
                    (match uu____2901 with
                     | (nm,body1) ->
                         let attrs =
                           FStar_List.map
                             (non_tail_inline_closure_env cfg env0)
                             lb.FStar_Syntax_Syntax.lbattrs
                            in
                         let lb1 =
                           let uu___372_2977 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___372_2977.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___372_2977.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs = attrs;
                             FStar_Syntax_Syntax.lbpos =
                               (uu___372_2977.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack1 t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2994,lbs),body) ->
                    let norm_one_lb env2 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____3060  -> fun env3  -> dummy :: env3)
                          lb.FStar_Syntax_Syntax.lbunivs env2
                         in
                      let env3 =
                        let uu____3077 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____3077
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____3092  -> fun env3  -> dummy :: env3)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____3116 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____3116
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___395_3127 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___395_3127.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___395_3127.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___398_3128 = lb  in
                      let uu____3129 =
                        non_tail_inline_closure_env cfg env3
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___398_3128.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___398_3128.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____3129;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___398_3128.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___398_3128.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env1))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____3161  -> fun env2  -> dummy :: env2)
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
            (fun uu____3253  ->
               let uu____3254 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3256 = env_to_string env1  in
               let uu____3258 = stack_to_string stack1  in
               let uu____3260 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 ">>> %s (env=%s, stack=%s)\nRebuild closure_as_term %s\n"
                 uu____3254 uu____3256 uu____3258 uu____3260);
          (match stack1 with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3267,uu____3268),aq,r))::stack2 ->
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
               let uu____3363 = close_binders cfg env' bs  in
               (match uu____3363 with
                | (bs1,uu____3379) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3399 =
                      let uu___465_3402 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___465_3402.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___465_3402.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env1 stack2 uu____3399)
           | (Match (env2,branches1,cfg1,r))::stack2 ->
               let close_one_branch env3 uu____3458 =
                 match uu____3458 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env4 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3573 ->
                           (p, env4)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3604 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3693  ->
                                     fun uu____3694  ->
                                       match (uu____3693, uu____3694) with
                                       | ((pats1,env5),(p1,b)) ->
                                           let uu____3844 = norm_pat env5 p1
                                              in
                                           (match uu____3844 with
                                            | (p2,env6) ->
                                                (((p2, b) :: pats1), env6)))
                                  ([], env4))
                              in
                           (match uu____3604 with
                            | (pats1,env5) ->
                                ((let uu___502_4014 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___502_4014.FStar_Syntax_Syntax.p)
                                  }), env5))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___506_4035 = x  in
                             let uu____4036 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___506_4035.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___506_4035.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4036
                             }  in
                           ((let uu___509_4050 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___509_4050.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___513_4061 = x  in
                             let uu____4062 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___513_4061.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___513_4061.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4062
                             }  in
                           ((let uu___516_4076 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___516_4076.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___522_4092 = x  in
                             let uu____4093 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___522_4092.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___522_4092.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4093
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env4 t1
                              in
                           ((let uu___526_4110 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___526_4110.FStar_Syntax_Syntax.p)
                             }), env4)
                        in
                     let uu____4115 = norm_pat env3 pat  in
                     (match uu____4115 with
                      | (pat1,env4) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____4184 =
                                  non_tail_inline_closure_env cfg1 env4 w  in
                                FStar_Pervasives_Native.Some uu____4184
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env4 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____4203 =
                   let uu____4204 =
                     let uu____4227 =
                       FStar_All.pipe_right branches1
                         (FStar_List.map (close_one_branch env2))
                        in
                     (t, uu____4227)  in
                   FStar_Syntax_Syntax.Tm_match uu____4204  in
                 mk uu____4203 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env2 stack2 t1
           | (Meta (env_m,m,r))::stack2 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names,args) ->
                     let uu____4363 =
                       let uu____4384 =
                         FStar_All.pipe_right names
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m))
                          in
                       let uu____4401 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1  ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4510  ->
                                         match uu____4510 with
                                         | (a,q) ->
                                             let uu____4537 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a
                                                in
                                             (uu____4537, q)))))
                          in
                       (uu____4384, uu____4401)  in
                     FStar_Syntax_Syntax.Meta_pattern uu____4363
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4566 =
                       let uu____4573 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4573)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4566
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4585 =
                       let uu____4594 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4594)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4585
                 | uu____4599 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env1 stack2 t1
           | uu____4605 -> failwith "Impossible: unexpected stack element")

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
            let uu____4621 =
              let uu____4622 = inline_closure_env cfg env1 [] t  in
              FStar_Syntax_Syntax.Meta uu____4622  in
            FStar_Pervasives_Native.Some uu____4621
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
        let uu____4639 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4723  ->
                  fun uu____4724  ->
                    match (uu____4723, uu____4724) with
                    | ((env2,out),(b,imp)) ->
                        let b1 =
                          let uu___581_4864 = b  in
                          let uu____4865 =
                            inline_closure_env cfg env2 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___581_4864.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___581_4864.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4865
                          }  in
                        let imp1 = close_imp cfg env2 imp  in
                        let env3 = dummy :: env2  in
                        (env3, ((b1, imp1) :: out))) (env1, []))
           in
        match uu____4639 with | (env2,bs1) -> ((FStar_List.rev bs1), env2)

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
        | uu____5007 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5020 = inline_closure_env cfg env1 [] t  in
                 let uu____5021 =
                   FStar_Option.map (norm_universe cfg env1) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5020 uu____5021
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5034 = inline_closure_env cfg env1 [] t  in
                 let uu____5035 =
                   FStar_Option.map (norm_universe cfg env1) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5034 uu____5035
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env1 []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5089  ->
                           match uu____5089 with
                           | (a,q) ->
                               let uu____5110 =
                                 inline_closure_env cfg env1 [] a  in
                               (uu____5110, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_5127  ->
                           match uu___5_5127 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5131 =
                                 inline_closure_env cfg env1 [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5131
                           | f -> f))
                    in
                 let uu____5135 =
                   let uu___614_5136 = c1  in
                   let uu____5137 =
                     FStar_List.map (norm_universe cfg env1)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5137;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___614_5136.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5135)

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
                   (fun uu___6_5155  ->
                      match uu___6_5155 with
                      | FStar_Syntax_Syntax.DECREASES uu____5157 -> false
                      | uu____5161 -> true))
               in
            let rc1 =
              let uu___626_5164 = rc  in
              let uu____5165 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env1 [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___626_5164.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5165;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5174 -> lopt

let (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___7_5195  ->
            match uu___7_5195 with
            | FStar_Syntax_Syntax.DECREASES uu____5197 -> false
            | uu____5201 -> true))
  
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
    let uu____5248 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____5248 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5287 = FStar_Syntax_Embeddings.unembed e t  in
        uu____5287 false FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'uuuuuu5307 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'uuuuuu5307) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env1  ->
      FStar_List.fold_right
        (fun uu____5369  ->
           fun subst  ->
             match uu____5369 with
             | (binder_opt,closure1) ->
                 (match (binder_opt, closure1) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env2,term,uu____5410,uu____5411)) ->
                      let uu____5472 = b  in
                      (match uu____5472 with
                       | (bv,uu____5480) ->
                           let uu____5481 =
                             let uu____5483 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5483  in
                           if uu____5481
                           then subst
                           else
                             (let term1 = closure_as_term cfg env2 term  in
                              let uu____5491 = unembed_binder term1  in
                              match uu____5491 with
                              | FStar_Pervasives_Native.None  -> subst
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5498 =
                                      let uu___666_5499 = bv  in
                                      let uu____5500 =
                                        FStar_Syntax_Subst.subst subst
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___666_5499.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___666_5499.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5500
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5498
                                     in
                                  let b_for_x =
                                    let uu____5506 =
                                      let uu____5513 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5513)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5506  in
                                  let subst1 =
                                    FStar_List.filter
                                      (fun uu___8_5529  ->
                                         match uu___8_5529 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5531,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5533;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5534;_})
                                             ->
                                             let uu____5539 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5539
                                         | uu____5541 -> true) subst
                                     in
                                  b_for_x :: subst1))
                  | uu____5543 -> subst)) env1 []
  
let reduce_primops :
  'uuuuuu5565 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5565)
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
            (let uu____5617 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5617 with
             | (head,args) ->
                 let uu____5662 =
                   let uu____5663 = FStar_Syntax_Util.un_uinst head  in
                   uu____5663.FStar_Syntax_Syntax.n  in
                 (match uu____5662 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5669 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5669 with
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
                                (fun uu____5692  ->
                                   let uu____5693 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5695 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5697 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5693 uu____5695 uu____5697);
                              tm)
                           else
                             (let uu____5702 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5702 with
                              | (args_1,args_2) ->
                                  let args_11 =
                                    FStar_List.map
                                      (fun uu____5860  ->
                                         match uu____5860 with
                                         | (targ,qual) ->
                                             let uu____5879 =
                                               FStar_Syntax_Util.unmeta targ
                                                in
                                             (uu____5879, qual)) args_1
                                     in
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5885  ->
                                        let uu____5886 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5886);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5891  ->
                                             if
                                               prim_step.FStar_TypeChecker_Cfg.requires_binder_substitution
                                             then mk_psc_subst cfg env1
                                             else [])
                                      }  in
                                    let r =
                                      prim_step.FStar_TypeChecker_Cfg.interpretation
                                        psc norm_cb args_11
                                       in
                                    match r with
                                    | FStar_Pervasives_Native.None  ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5905  ->
                                              let uu____5906 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5906);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5914  ->
                                              let uu____5915 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5917 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5915 uu____5917);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5920 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5924  ->
                                 let uu____5925 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5925);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5931  ->
                            let uu____5932 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5932);
                       (match args with
                        | (a1,uu____5938)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5963 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5977  ->
                            let uu____5978 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5978);
                       (match args with
                        | (t,uu____5984)::(r,uu____5986)::[] ->
                            let uu____6027 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____6027 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____6033 -> tm))
                  | uu____6044 -> tm))
  
let reduce_equality :
  'uuuuuu6056 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu6056)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun env1  ->
        fun tm  ->
          reduce_primops norm_cb
            (let uu___759_6106 = cfg  in
             {
               FStar_TypeChecker_Cfg.steps =
                 (let uu___761_6109 = FStar_TypeChecker_Cfg.default_steps  in
                  {
                    FStar_TypeChecker_Cfg.beta =
                      (uu___761_6109.FStar_TypeChecker_Cfg.beta);
                    FStar_TypeChecker_Cfg.iota =
                      (uu___761_6109.FStar_TypeChecker_Cfg.iota);
                    FStar_TypeChecker_Cfg.zeta =
                      (uu___761_6109.FStar_TypeChecker_Cfg.zeta);
                    FStar_TypeChecker_Cfg.zeta_full =
                      (uu___761_6109.FStar_TypeChecker_Cfg.zeta_full);
                    FStar_TypeChecker_Cfg.weak =
                      (uu___761_6109.FStar_TypeChecker_Cfg.weak);
                    FStar_TypeChecker_Cfg.hnf =
                      (uu___761_6109.FStar_TypeChecker_Cfg.hnf);
                    FStar_TypeChecker_Cfg.primops = true;
                    FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                      (uu___761_6109.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                    FStar_TypeChecker_Cfg.unfold_until =
                      (uu___761_6109.FStar_TypeChecker_Cfg.unfold_until);
                    FStar_TypeChecker_Cfg.unfold_only =
                      (uu___761_6109.FStar_TypeChecker_Cfg.unfold_only);
                    FStar_TypeChecker_Cfg.unfold_fully =
                      (uu___761_6109.FStar_TypeChecker_Cfg.unfold_fully);
                    FStar_TypeChecker_Cfg.unfold_attr =
                      (uu___761_6109.FStar_TypeChecker_Cfg.unfold_attr);
                    FStar_TypeChecker_Cfg.unfold_tac =
                      (uu___761_6109.FStar_TypeChecker_Cfg.unfold_tac);
                    FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                      (uu___761_6109.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                    FStar_TypeChecker_Cfg.simplify =
                      (uu___761_6109.FStar_TypeChecker_Cfg.simplify);
                    FStar_TypeChecker_Cfg.erase_universes =
                      (uu___761_6109.FStar_TypeChecker_Cfg.erase_universes);
                    FStar_TypeChecker_Cfg.allow_unbound_universes =
                      (uu___761_6109.FStar_TypeChecker_Cfg.allow_unbound_universes);
                    FStar_TypeChecker_Cfg.reify_ =
                      (uu___761_6109.FStar_TypeChecker_Cfg.reify_);
                    FStar_TypeChecker_Cfg.compress_uvars =
                      (uu___761_6109.FStar_TypeChecker_Cfg.compress_uvars);
                    FStar_TypeChecker_Cfg.no_full_norm =
                      (uu___761_6109.FStar_TypeChecker_Cfg.no_full_norm);
                    FStar_TypeChecker_Cfg.check_no_uvars =
                      (uu___761_6109.FStar_TypeChecker_Cfg.check_no_uvars);
                    FStar_TypeChecker_Cfg.unmeta =
                      (uu___761_6109.FStar_TypeChecker_Cfg.unmeta);
                    FStar_TypeChecker_Cfg.unascribe =
                      (uu___761_6109.FStar_TypeChecker_Cfg.unascribe);
                    FStar_TypeChecker_Cfg.in_full_norm_request =
                      (uu___761_6109.FStar_TypeChecker_Cfg.in_full_norm_request);
                    FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                      (uu___761_6109.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                    FStar_TypeChecker_Cfg.nbe_step =
                      (uu___761_6109.FStar_TypeChecker_Cfg.nbe_step);
                    FStar_TypeChecker_Cfg.for_extraction =
                      (uu___761_6109.FStar_TypeChecker_Cfg.for_extraction)
                  });
               FStar_TypeChecker_Cfg.tcenv =
                 (uu___759_6106.FStar_TypeChecker_Cfg.tcenv);
               FStar_TypeChecker_Cfg.debug =
                 (uu___759_6106.FStar_TypeChecker_Cfg.debug);
               FStar_TypeChecker_Cfg.delta_level =
                 (uu___759_6106.FStar_TypeChecker_Cfg.delta_level);
               FStar_TypeChecker_Cfg.primitive_steps =
                 FStar_TypeChecker_Cfg.equality_ops;
               FStar_TypeChecker_Cfg.strong =
                 (uu___759_6106.FStar_TypeChecker_Cfg.strong);
               FStar_TypeChecker_Cfg.memoize_lazy =
                 (uu___759_6106.FStar_TypeChecker_Cfg.memoize_lazy);
               FStar_TypeChecker_Cfg.normalize_pure_lets =
                 (uu___759_6106.FStar_TypeChecker_Cfg.normalize_pure_lets);
               FStar_TypeChecker_Cfg.reifying =
                 (uu___759_6106.FStar_TypeChecker_Cfg.reifying)
             }) env1 tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____6120 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____6131 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____6142 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd  ->
    fun args  ->
      let aux min_args =
        let uu____6163 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____6163
          (fun n  ->
             if n < min_args
             then Norm_request_none
             else
               if n = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____6195 =
        let uu____6196 = FStar_Syntax_Util.un_uinst hd  in
        uu____6196.FStar_Syntax_Syntax.n  in
      match uu____6195 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu____6205 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____6214 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____6214)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd  ->
    fun args  ->
      let uu____6227 =
        let uu____6228 = FStar_Syntax_Util.un_uinst hd  in
        uu____6228.FStar_Syntax_Syntax.n  in
      match uu____6227 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6286 = FStar_Syntax_Util.mk_app hd [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____6286 rest
           | uu____6313 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6353 = FStar_Syntax_Util.mk_app hd [t]  in
               FStar_Syntax_Util.mk_app uu____6353 rest
           | uu____6372 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____6446 = FStar_Syntax_Util.mk_app hd [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____6446 rest
           | uu____6481 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6483 ->
          let uu____6484 =
            let uu____6486 = FStar_Syntax_Print.term_to_string hd  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6486
             in
          failwith uu____6484
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6507  ->
    match uu___9_6507 with
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
        let uu____6514 =
          let uu____6517 =
            let uu____6518 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6518  in
          [uu____6517]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6514
    | FStar_Syntax_Embeddings.UnfoldFully names ->
        let uu____6526 =
          let uu____6529 =
            let uu____6530 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldFully uu____6530  in
          [uu____6529]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6526
    | FStar_Syntax_Embeddings.UnfoldAttr names ->
        let uu____6538 =
          let uu____6541 =
            let uu____6542 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6542  in
          [uu____6541]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6538
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s  ->
    let s1 = FStar_List.concatMap tr_norm_step s  in
    let add_exclude s2 z =
      let uu____6578 =
        FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2  in
      if uu____6578 then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2  in
    let s2 = FStar_TypeChecker_Env.Beta :: s1  in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta  in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota  in s4
  
let get_norm_request :
  'uuuuuu6603 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu6603) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6654 =
            let uu____6659 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6659 s  in
          match uu____6654 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6675 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6675
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
        | uu____6710::(tm,uu____6712)::[] ->
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
        | (tm,uu____6741)::[] ->
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
        | (steps,uu____6762)::uu____6763::(tm,uu____6765)::[] ->
            let uu____6786 =
              let uu____6791 = full_norm steps  in parse_steps uu____6791  in
            (match uu____6786 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s), tm))
        | uu____6821 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6853 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6860  ->
                    match uu___10_6860 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6862 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6864 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6868 -> true
                    | uu____6872 -> false))
             in
          if uu____6853
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6882  ->
             let uu____6883 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6883);
        (let tm_norm =
           let uu____6887 =
             let uu____6902 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6902.FStar_TypeChecker_Env.nbe  in
           uu____6887 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6906  ->
              let uu____6907 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6907);
         tm_norm)
  
let firstn :
  'uuuuuu6917 .
    Prims.int ->
      'uuuuuu6917 Prims.list ->
        ('uuuuuu6917 Prims.list * 'uuuuuu6917 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack1  ->
      let rec drop_irrel uu___11_6974 =
        match uu___11_6974 with
        | (MemoLazy uu____6979)::s -> drop_irrel s
        | (UnivArgs uu____6989)::s -> drop_irrel s
        | s -> s  in
      let uu____7002 = drop_irrel stack1  in
      match uu____7002 with
      | (App
          (uu____7006,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____7007;
                        FStar_Syntax_Syntax.vars = uu____7008;_},uu____7009,uu____7010))::uu____7011
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____7016 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____7045) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____7055) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____7076  ->
                  match uu____7076 with
                  | (a,uu____7087) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____7098 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____7115 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____7117 -> false
    | FStar_Syntax_Syntax.Tm_type uu____7131 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____7133 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____7135 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____7137 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____7139 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____7142 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____7150 -> false
    | FStar_Syntax_Syntax.Tm_let uu____7158 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____7173 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____7193 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____7209 -> true
    | FStar_Syntax_Syntax.Tm_match uu____7217 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7289  ->
                   match uu____7289 with
                   | (a,uu____7300) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7311) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____7410,args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7465  ->
                        match uu____7465 with
                        | (a,uu____7476) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7485,uu____7486,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7492,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7498 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7508 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7510 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7521 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7532 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7543 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7554 -> false
  
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
            let uu____7587 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7587 with
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
              (fun uu____7786  ->
                 fun uu____7787  ->
                   match (uu____7786, uu____7787) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7893 =
            match uu____7893 with
            | (x,y,z) ->
                let uu____7913 = FStar_Util.string_of_bool x  in
                let uu____7915 = FStar_Util.string_of_bool y  in
                let uu____7917 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7913 uu____7915
                  uu____7917
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7945  ->
                    let uu____7946 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7948 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7946 uu____7948);
               if b then reif else no)
            else
              if
                (let uu____7963 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7963)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7968  ->
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
                          ((is_rec,uu____8003),uu____8004);
                        FStar_Syntax_Syntax.sigrng = uu____8005;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____8007;
                        FStar_Syntax_Syntax.sigattrs = uu____8008;
                        FStar_Syntax_Syntax.sigopts = uu____8009;_},uu____8010),uu____8011),uu____8012,uu____8013,uu____8014)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8123  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____8125,uu____8126,uu____8127,uu____8128) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8195  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____8198),uu____8199);
                        FStar_Syntax_Syntax.sigrng = uu____8200;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____8202;
                        FStar_Syntax_Syntax.sigattrs = uu____8203;
                        FStar_Syntax_Syntax.sigopts = uu____8204;_},uu____8205),uu____8206),uu____8207,uu____8208,uu____8209)
                     when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8318  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8320,FStar_Pervasives_Native.Some
                    uu____8321,uu____8322,uu____8323) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8391  ->
                           let uu____8392 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8392);
                      (let uu____8395 =
                         let uu____8407 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8433 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8433
                            in
                         let uu____8445 =
                           let uu____8457 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8483 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8483
                              in
                           let uu____8499 =
                             let uu____8511 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8537 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8537
                                in
                             [uu____8511]  in
                           uu____8457 :: uu____8499  in
                         uu____8407 :: uu____8445  in
                       comb_or uu____8395))
                 | (uu____8585,uu____8586,FStar_Pervasives_Native.Some
                    uu____8587,uu____8588) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8656  ->
                           let uu____8657 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8657);
                      (let uu____8660 =
                         let uu____8672 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8698 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8698
                            in
                         let uu____8710 =
                           let uu____8722 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8748 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8748
                              in
                           let uu____8764 =
                             let uu____8776 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8802 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8802
                                in
                             [uu____8776]  in
                           uu____8722 :: uu____8764  in
                         uu____8672 :: uu____8710  in
                       comb_or uu____8660))
                 | (uu____8850,uu____8851,uu____8852,FStar_Pervasives_Native.Some
                    uu____8853) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8921  ->
                           let uu____8922 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8922);
                      (let uu____8925 =
                         let uu____8937 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8963 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8963
                            in
                         let uu____8975 =
                           let uu____8987 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____9013 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____9013
                              in
                           let uu____9029 =
                             let uu____9041 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____9067 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____9067
                                in
                             [uu____9041]  in
                           uu____8987 :: uu____9029  in
                         uu____8937 :: uu____8975  in
                       comb_or uu____8925))
                 | uu____9115 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____9161  ->
                           let uu____9162 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____9164 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____9166 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____9162 uu____9164 uu____9166);
                      (let uu____9169 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_9175  ->
                                 match uu___12_9175 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____9181 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____9181 l))
                          in
                       FStar_All.pipe_left yesno uu____9169)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____9197  ->
               let uu____9198 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____9200 =
                 let uu____9202 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____9202  in
               let uu____9203 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____9198 uu____9200 uu____9203);
          (match res with
           | (false ,uu____9206,uu____9207) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____9232 ->
               let uu____9242 =
                 let uu____9244 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9244
                  in
               FStar_All.pipe_left failwith uu____9242)
  
let decide_unfolding :
  'uuuuuu9263 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'uuuuuu9263 ->
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
                    let uu___1170_9332 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1172_9335 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1172_9335.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1172_9335.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1170_9332.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1170_9332.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1170_9332.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1170_9332.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1170_9332.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1170_9332.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1170_9332.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1170_9332.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____9397 = push e t  in (UnivArgs (us, r)) ::
                          uu____9397
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9409 =
                      let uu____9416 =
                        let uu____9417 =
                          let uu____9418 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____9418  in
                        FStar_Syntax_Syntax.Tm_constant uu____9417  in
                      FStar_Syntax_Syntax.mk uu____9416  in
                    uu____9409 FStar_Pervasives_Native.None
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
    let uu____9484 =
      let uu____9485 = FStar_Syntax_Subst.compress t  in
      uu____9485.FStar_Syntax_Syntax.n  in
    match uu____9484 with
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____9516 =
          let uu____9517 = FStar_Syntax_Util.un_uinst hd  in
          uu____9517.FStar_Syntax_Syntax.n  in
        (match uu____9516 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9534 =
                 let uu____9541 =
                   let uu____9552 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9552 FStar_List.tl  in
                 FStar_All.pipe_right uu____9541 FStar_List.hd  in
               FStar_All.pipe_right uu____9534 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9651 -> FStar_Pervasives_Native.None)
    | uu____9652 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9931 ->
                   let uu____9946 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9946
               | uu____9949 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9959  ->
               let uu____9960 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9962 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9964 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9966 =
                 FStar_Util.string_of_int (FStar_List.length env1)  in
               let uu____9974 =
                 let uu____9976 =
                   let uu____9979 = firstn (Prims.of_int (4)) stack1  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9979
                    in
                 stack_to_string uu____9976  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9960 uu____9962 uu____9964 uu____9966 uu____9974);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____10007  ->
               let uu____10008 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____10008);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____10014  ->
                     let uu____10015 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____10015);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____10018 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____10022  ->
                     let uu____10023 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____10023);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____10026 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____10030  ->
                     let uu____10031 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____10031);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____10034 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____10038  ->
                     let uu____10039 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____10039);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10042;
                 FStar_Syntax_Syntax.fv_delta = uu____10043;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____10047  ->
                     let uu____10048 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____10048);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10051;
                 FStar_Syntax_Syntax.fv_delta = uu____10052;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____10053);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____10063  ->
                     let uu____10064 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____10064);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____10070 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____10070 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level uu____10073)
                    when uu____10073 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____10077  ->
                          let uu____10078 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____10078);
                     rebuild cfg env1 stack1 t1)
                | uu____10081 ->
                    let uu____10084 =
                      decide_unfolding cfg env1 stack1
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____10084 with
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
               let uu____10123 = closure_as_term cfg env1 t2  in
               rebuild cfg env1 stack1 uu____10123
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10151 = is_norm_request hd args  in
                  uu____10151 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____10157 = rejig_norm_request hd args  in
                 norm cfg env1 stack1 uu____10157))
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10185 = is_norm_request hd args  in
                  uu____10185 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1283_10192 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1285_10195 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1285_10195.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1283_10192.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1283_10192.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1283_10192.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1283_10192.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1283_10192.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1283_10192.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____10202 =
                   get_norm_request cfg (norm cfg' env1 []) args  in
                 match uu____10202 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack2 =
                         FStar_All.pipe_right stack1
                           (FStar_List.fold_right
                              (fun uu____10238  ->
                                 fun stack2  ->
                                   match uu____10238 with
                                   | (a,aq) ->
                                       let uu____10250 =
                                         let uu____10251 =
                                           let uu____10258 =
                                             let uu____10259 =
                                               let uu____10291 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env1, a, uu____10291, false)
                                                in
                                             Clos uu____10259  in
                                           (uu____10258, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10251  in
                                       uu____10250 :: stack2) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10359  ->
                            let uu____10360 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10360);
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
                         let uu____10392 =
                           let uu____10394 =
                             let uu____10396 = FStar_Util.time_diff start fin
                                in
                             FStar_Pervasives_Native.snd uu____10396  in
                           FStar_Util.string_of_int uu____10394  in
                         let uu____10403 =
                           FStar_Syntax_Print.term_to_string tm'  in
                         let uu____10405 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                         let uu____10407 =
                           FStar_Syntax_Print.term_to_string tm_norm  in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____10392 uu____10403 uu____10405 uu____10407)
                      else ();
                      rebuild cfg env1 stack1 tm_norm)
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     let delta_level =
                       let uu____10427 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___13_10434  ->
                                 match uu___13_10434 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____10436 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____10438 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____10442 -> true
                                 | uu____10446 -> false))
                          in
                       if uu____10427
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let cfg'1 =
                       let uu___1323_10454 = cfg  in
                       let uu____10455 =
                         let uu___1325_10456 =
                           FStar_TypeChecker_Cfg.to_fsteps s  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1325_10456.FStar_TypeChecker_Cfg.for_extraction)
                         }  in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____10455;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1323_10454.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1323_10454.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1323_10454.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1323_10454.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1323_10454.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___1323_10454.FStar_TypeChecker_Cfg.reifying)
                       }  in
                     let stack' =
                       let tail = (Cfg cfg) :: stack1  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____10464 =
                           let uu____10465 =
                             let uu____10470 = FStar_Util.now ()  in
                             (tm, uu____10470)  in
                           Debug uu____10465  in
                         uu____10464 :: tail
                       else tail  in
                     norm cfg'1 env1 stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env1 u  in
               let uu____10475 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env1 stack1 uu____10475
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env1 stack1 t'
               else
                 (let us1 =
                    let uu____10486 =
                      let uu____10493 =
                        FStar_List.map (norm_universe cfg env1) us  in
                      (uu____10493, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10486  in
                  let stack2 = us1 :: stack1  in norm cfg env1 stack2 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10502 = lookup_bvar env1 x  in
               (match uu____10502 with
                | Univ uu____10503 ->
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
                      let uu____10557 = FStar_ST.op_Bang r  in
                      (match uu____10557 with
                       | FStar_Pervasives_Native.Some (env3,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10653  ->
                                 let uu____10654 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10656 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10654
                                   uu____10656);
                            (let uu____10659 = maybe_weakly_reduced t'  in
                             if uu____10659
                             then
                               match stack1 with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env3 stack1 t'
                               | uu____10662 -> norm cfg env3 stack1 t'
                             else rebuild cfg env3 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env2 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env2 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____10706)::uu____10707 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10718,uu____10719))::stack_rest ->
                    (match c with
                     | Univ uu____10723 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env1)
                           stack_rest t1
                     | uu____10732 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10762  ->
                                    let uu____10763 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10763);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env1) stack_rest body)
                          | b::tl ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10799  ->
                                    let uu____10800 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10800);
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
                       (fun uu____10848  ->
                          let uu____10849 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10849);
                     norm cfg env1 stack2 t1)
                | (Match uu____10852)::uu____10853 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10868 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10868 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____10904  -> dummy :: env2) env1)
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
                                          let uu____10948 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10948)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1447_10956 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1447_10956.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1447_10956.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10957 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10963  ->
                                 let uu____10964 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10964);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1454_10979 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1454_10979.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1454_10979.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1454_10979.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1454_10979.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1454_10979.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1454_10979.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1454_10979.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1454_10979.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Debug uu____10983)::uu____10984 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10995 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10995 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11031  -> dummy :: env2) env1)
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
                                          let uu____11075 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11075)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1447_11083 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1447_11083.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1447_11083.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11084 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11090  ->
                                 let uu____11091 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11091);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1454_11106 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1454_11106.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1454_11106.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1454_11106.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1454_11106.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1454_11106.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1454_11106.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1454_11106.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1454_11106.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11110)::uu____11111 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11124 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11124 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11160  -> dummy :: env2) env1)
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
                                          let uu____11204 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11204)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1447_11212 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1447_11212.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1447_11212.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11213 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11219  ->
                                 let uu____11220 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11220);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1454_11235 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1454_11235.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1454_11235.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1454_11235.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1454_11235.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1454_11235.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1454_11235.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1454_11235.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1454_11235.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11239)::uu____11240 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11255 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11255 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11291  -> dummy :: env2) env1)
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
                                          let uu____11335 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11335)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1447_11343 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1447_11343.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1447_11343.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11344 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11350  ->
                                 let uu____11351 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11351);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1454_11366 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1454_11366.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1454_11366.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1454_11366.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1454_11366.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1454_11366.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1454_11366.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1454_11366.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1454_11366.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11370)::uu____11371 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11386 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11386 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11422  -> dummy :: env2) env1)
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
                                          let uu____11466 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11466)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1447_11474 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1447_11474.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1447_11474.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11475 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11481  ->
                                 let uu____11482 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11482);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1454_11497 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1454_11497.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1454_11497.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1454_11497.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1454_11497.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1454_11497.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1454_11497.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1454_11497.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1454_11497.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (CBVApp uu____11501)::uu____11502 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11517 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11517 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11553  -> dummy :: env2) env1)
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
                                          let uu____11597 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11597)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1447_11605 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1447_11605.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1447_11605.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11606 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11612  ->
                                 let uu____11613 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11613);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1454_11628 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1454_11628.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1454_11628.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1454_11628.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1454_11628.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1454_11628.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1454_11628.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1454_11628.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1454_11628.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____11632)::uu____11633 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11652 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11652 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11688  -> dummy :: env2) env1)
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
                                          let uu____11732 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11732)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1447_11740 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1447_11740.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1447_11740.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11741 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11747  ->
                                 let uu____11748 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11748);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1454_11763 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1454_11763.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1454_11763.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1454_11763.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1454_11763.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1454_11763.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1454_11763.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1454_11763.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1454_11763.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____11771 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11771 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11807  -> dummy :: env2) env1)
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
                                          let uu____11851 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11851)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1447_11859 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1447_11859.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1447_11859.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11860 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11866  ->
                                 let uu____11867 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11867);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1454_11882 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1454_11882.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1454_11882.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1454_11882.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1454_11882.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1454_11882.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1454_11882.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1454_11882.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1454_11882.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head,args) ->
               let strict_args =
                 let uu____11918 =
                   let uu____11919 = FStar_Syntax_Util.un_uinst head  in
                   uu____11919.FStar_Syntax_Syntax.n  in
                 match uu____11918 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11928 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____11949  ->
                              fun stack2  ->
                                match uu____11949 with
                                | (a,aq) ->
                                    let uu____11961 =
                                      let uu____11962 =
                                        let uu____11969 =
                                          let uu____11970 =
                                            let uu____12002 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env1, a, uu____12002, false)  in
                                          Clos uu____11970  in
                                        (uu____11969, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11962  in
                                    uu____11961 :: stack2) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12070  ->
                          let uu____12071 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12071);
                     norm cfg env1 stack2 head)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____12122  ->
                              match uu____12122 with
                              | (a,i) ->
                                  let uu____12133 = norm cfg env1 [] a  in
                                  (uu____12133, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____12139 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____12154 = FStar_List.nth norm_args i
                                    in
                                 match uu____12154 with
                                 | (arg_i,uu____12165) ->
                                     let uu____12166 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____12166 with
                                      | (head1,uu____12185) ->
                                          let uu____12210 =
                                            let uu____12211 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____12211.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____12210 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____12215 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____12218 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____12218
                                           | uu____12219 -> false)))))
                       in
                    if uu____12139
                    then
                      let stack2 =
                        FStar_All.pipe_right stack1
                          (FStar_List.fold_right
                             (fun uu____12236  ->
                                fun stack2  ->
                                  match uu____12236 with
                                  | (a,aq) ->
                                      let uu____12248 =
                                        let uu____12249 =
                                          let uu____12256 =
                                            let uu____12257 =
                                              let uu____12289 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env1, a, uu____12289, false)
                                               in
                                            Clos uu____12257  in
                                          (uu____12256, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____12249  in
                                      uu____12248 :: stack2) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12371  ->
                            let uu____12372 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12372);
                       norm cfg env1 stack2 head)
                    else
                      (let head1 = closure_as_term cfg env1 head  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head1 norm_args
                           FStar_Pervasives_Native.None
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env1 stack1 term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12392) when
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
                             ((let uu___1516_12437 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1516_12437.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1516_12437.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env1 stack1 t2
                  | uu____12438 ->
                      let uu____12453 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 uu____12453)
               else
                 (let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12457 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12457 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env1) [] f1  in
                      let t2 =
                        let uu____12488 =
                          let uu____12489 =
                            let uu____12496 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1525_12502 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1525_12502.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1525_12502.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12496)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12489  in
                        mk uu____12488 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12526 = closure_as_term cfg env1 t1  in
                 rebuild cfg env1 stack1 uu____12526
               else
                 (let uu____12529 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12529 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12537 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env2  ->
                                  fun uu____12563  -> dummy :: env2) env1)
                           in
                        norm_comp cfg uu____12537 c1  in
                      let t2 =
                        let uu____12587 = norm_binders cfg env1 bs1  in
                        FStar_Syntax_Util.arrow uu____12587 c2  in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env1 stack1 t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12700)::uu____12701 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12714  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (Arg uu____12716)::uu____12717 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12728  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (App
                    (uu____12730,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12731;
                                   FStar_Syntax_Syntax.vars = uu____12732;_},uu____12733,uu____12734))::uu____12735
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12742  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (MemoLazy uu____12744)::uu____12745 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12756  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | uu____12758 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12761  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env1 [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12766  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12792 = norm cfg env1 [] t2  in
                             FStar_Util.Inl uu____12792
                         | FStar_Util.Inr c ->
                             let uu____12806 = norm_comp cfg env1 c  in
                             FStar_Util.Inr uu____12806
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env1 [])  in
                       match stack1 with
                       | (Cfg cfg1)::stack2 ->
                           let t2 =
                             let uu____12829 =
                               let uu____12830 =
                                 let uu____12857 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12857, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12830
                                in
                             mk uu____12829 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env1 stack2 t2
                       | uu____12892 ->
                           let uu____12893 =
                             let uu____12894 =
                               let uu____12895 =
                                 let uu____12922 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12922, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12895
                                in
                             mk uu____12894 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env1 stack1 uu____12893))))
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
                   let uu___1604_13000 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1606_13003 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1606_13003.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1604_13000.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1604_13000.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1604_13000.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1604_13000.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1604_13000.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1604_13000.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1604_13000.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1604_13000.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____13044 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____13044 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1619_13064 = cfg  in
                               let uu____13065 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1619_13064.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____13065;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1619_13064.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1619_13064.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1619_13064.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1619_13064.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1619_13064.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1619_13064.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1619_13064.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____13072 =
                                 let uu____13073 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env1 [] uu____13073  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13072
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1626_13076 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1626_13076.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1626_13076.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1626_13076.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1626_13076.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____13077 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env1 stack1 uu____13077
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13090,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13091;
                               FStar_Syntax_Syntax.lbunivs = uu____13092;
                               FStar_Syntax_Syntax.lbtyp = uu____13093;
                               FStar_Syntax_Syntax.lbeff = uu____13094;
                               FStar_Syntax_Syntax.lbdef = uu____13095;
                               FStar_Syntax_Syntax.lbattrs = uu____13096;
                               FStar_Syntax_Syntax.lbpos = uu____13097;_}::uu____13098),uu____13099)
               -> rebuild cfg env1 stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let uu____13144 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
               if uu____13144
               then
                 let binder =
                   let uu____13148 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13148  in
                 let env2 =
                   let uu____13158 =
                     let uu____13165 =
                       let uu____13166 =
                         let uu____13198 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env1, (lb.FStar_Syntax_Syntax.lbdef), uu____13198,
                           false)
                          in
                       Clos uu____13166  in
                     ((FStar_Pervasives_Native.Some binder), uu____13165)  in
                   uu____13158 :: env1  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____13273  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env2 stack1 body)
               else
                 (let uu____13277 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu____13280 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff
                          in
                       FStar_Syntax_Util.is_div_effect uu____13280)
                     in
                  if uu____13277
                  then
                    let ffun =
                      let uu____13285 =
                        let uu____13292 =
                          let uu____13293 =
                            let uu____13312 =
                              let uu____13321 =
                                let uu____13328 =
                                  FStar_All.pipe_right
                                    lb.FStar_Syntax_Syntax.lbname
                                    FStar_Util.left
                                   in
                                FStar_Syntax_Syntax.mk_binder uu____13328  in
                              [uu____13321]  in
                            (uu____13312, body, FStar_Pervasives_Native.None)
                             in
                          FStar_Syntax_Syntax.Tm_abs uu____13293  in
                        FStar_Syntax_Syntax.mk uu____13292  in
                      uu____13285 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    let stack2 =
                      (CBVApp
                         (env1, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack1  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____13362  ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env1 stack2 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____13369  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____13371 = closure_as_term cfg env1 t1  in
                        rebuild cfg env1 stack1 uu____13371))
                    else
                      (let uu____13374 =
                         let uu____13379 =
                           let uu____13380 =
                             let uu____13387 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____13387
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____13380]  in
                         FStar_Syntax_Subst.open_term uu____13379 body  in
                       match uu____13374 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____13414  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____13423 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____13423  in
                               FStar_Util.Inl
                                 (let uu___1672_13439 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1672_13439.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1672_13439.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____13442  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1677_13445 = lb  in
                                let uu____13446 =
                                  norm cfg env1 []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____13449 =
                                  FStar_List.map (norm cfg env1 [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1677_13445.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1677_13445.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____13446;
                                  FStar_Syntax_Syntax.lbattrs = uu____13449;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1677_13445.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____13484  -> dummy :: env2)
                                     env1)
                                 in
                              let stack2 = (Cfg cfg) :: stack1  in
                              let cfg1 =
                                let uu___1684_13509 = cfg  in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1684_13509.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1684_13509.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1684_13509.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1684_13509.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1684_13509.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1684_13509.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1684_13509.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1684_13509.FStar_TypeChecker_Cfg.reifying)
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____13513  ->
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
               let uu____13534 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13534 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp
                              in
                           let lbname =
                             let uu____13570 =
                               let uu___1700_13571 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1700_13571.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1700_13571.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13570  in
                           let uu____13572 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13572 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env1 xs  in
                               let env2 =
                                 let uu____13598 =
                                   FStar_List.map (fun uu____13620  -> dummy)
                                     xs1
                                    in
                                 let uu____13627 =
                                   let uu____13636 =
                                     FStar_List.map
                                       (fun uu____13652  -> dummy) lbs1
                                      in
                                   FStar_List.append uu____13636 env1  in
                                 FStar_List.append uu____13598 uu____13627
                                  in
                               let def_body1 = norm cfg env2 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13672 =
                                       let uu___1714_13673 = rc  in
                                       let uu____13674 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env2 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1714_13673.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13674;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1714_13673.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13672
                                 | uu____13683 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1719_13689 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1719_13689.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1719_13689.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1719_13689.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1719_13689.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13699 =
                        FStar_List.map (fun uu____13715  -> dummy) lbs2  in
                      FStar_List.append uu____13699 env1  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13723 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13723 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1728_13739 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1728_13739.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1728_13739.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env1 stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu____13773 = closure_as_term cfg env1 t1  in
               rebuild cfg env1 stack1 uu____13773
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13794 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13872  ->
                        match uu____13872 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1744_13997 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1744_13997.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1744_13997.FStar_Syntax_Syntax.sort)
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
               (match uu____13794 with
                | (rec_env,memos,uu____14188) ->
                    let uu____14243 =
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
                             let uu____14492 =
                               let uu____14499 =
                                 let uu____14500 =
                                   let uu____14532 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14532, false)
                                    in
                                 Clos uu____14500  in
                               (FStar_Pervasives_Native.None, uu____14499)
                                in
                             uu____14492 :: env2)
                        (FStar_Pervasives_Native.snd lbs) env1
                       in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14617  ->
                     let uu____14618 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14618);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14642 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env1 stack1 head
                     else
                       (match stack1 with
                        | uu____14646::uu____14647 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14652) ->
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
                             | uu____14731 -> norm cfg env1 stack1 head)
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
                                  let uu____14779 =
                                    let uu____14800 =
                                      norm_pattern_args cfg env1 args  in
                                    (names1, uu____14800)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14779
                              | uu____14829 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head1, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env1 stack1 t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14835 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env1 stack1 t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14851 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14865 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14879 =
                        let uu____14881 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14883 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14881 uu____14883
                         in
                      failwith uu____14879
                    else
                      (let uu____14888 = inline_closure_env cfg env1 [] t2
                          in
                       rebuild cfg env1 stack1 uu____14888)
                | uu____14889 -> norm cfg env1 stack1 t2))

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
              let uu____14898 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14898 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14912  ->
                        let uu____14913 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14913);
                   rebuild cfg env1 stack1 t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14926  ->
                        let uu____14927 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14929 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14927 uu____14929);
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
                      | (UnivArgs (us',uu____14942))::stack2 ->
                          ((let uu____14951 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14951
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14959 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14959) us'
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
                      | uu____14995 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env1 stack1 t1
                      | uu____14998 ->
                          let uu____15001 =
                            let uu____15003 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____15003
                             in
                          failwith uu____15001
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
              let uu____15023 =
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
                    let uu___1855_15041 = cfg  in
                    let uu____15042 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps
                       in
                    {
                      FStar_TypeChecker_Cfg.steps = uu____15042;
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1855_15041.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1855_15041.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        [FStar_TypeChecker_Env.InliningDelta;
                        FStar_TypeChecker_Env.Eager_unfolding_only];
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1855_15041.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1855_15041.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1855_15041.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1855_15041.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1855_15041.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  (cfg', ((Cfg cfg) :: stack1))
                else (cfg, stack1)  in
              match uu____15023 with
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
                     (uu____15083,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____15084;
                                    FStar_Syntax_Syntax.vars = uu____15085;_},uu____15086,uu____15087))::uu____15088
                     -> ()
                 | uu____15093 ->
                     let uu____15096 =
                       let uu____15098 = stack_to_string stack1  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____15098
                        in
                     failwith uu____15096);
                (let top0 = top  in
                 let top1 = FStar_Syntax_Util.unascribe top  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____15107  ->
                      let uu____15108 = FStar_Syntax_Print.tag_of_term top1
                         in
                      let uu____15110 =
                        FStar_Syntax_Print.term_to_string top1  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____15108
                        uu____15110);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1  in
                  let uu____15114 =
                    let uu____15115 = FStar_Syntax_Subst.compress top2  in
                    uu____15115.FStar_Syntax_Syntax.n  in
                  match uu____15114 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m
                         in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name
                         in
                      let uu____15137 =
                        let uu____15146 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr
                           in
                        FStar_All.pipe_right uu____15146 FStar_Util.must  in
                      (match uu____15137 with
                       | (uu____15161,repr) ->
                           let uu____15171 =
                             let uu____15178 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr
                                in
                             FStar_All.pipe_right uu____15178 FStar_Util.must
                              in
                           (match uu____15171 with
                            | (uu____15215,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15221 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15232 =
                                         let uu____15233 =
                                           FStar_Syntax_Subst.compress e  in
                                         uu____15233.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15232 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15239,uu____15240))
                                           ->
                                           let uu____15249 =
                                             let uu____15250 =
                                               FStar_Syntax_Subst.compress e1
                                                in
                                             uu____15250.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____15249 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15256,msrc,uu____15258))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15267 =
                                                  FStar_Syntax_Subst.compress
                                                    e2
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____15267
                                            | uu____15268 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15269 ->
                                           FStar_Pervasives_Native.None
                                        in
                                     let uu____15270 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     (match uu____15270 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___1934_15275 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___1934_15275.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___1934_15275.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___1934_15275.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e;
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___1934_15275.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___1934_15275.FStar_Syntax_Syntax.lbpos)
                                            }  in
                                          let uu____15276 =
                                            FStar_List.tl stack1  in
                                          let uu____15277 =
                                            let uu____15278 =
                                              let uu____15285 =
                                                let uu____15286 =
                                                  let uu____15300 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body
                                                     in
                                                  ((false, [lb1]),
                                                    uu____15300)
                                                   in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15286
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15285
                                               in
                                            uu____15278
                                              FStar_Pervasives_Native.None
                                              top2.FStar_Syntax_Syntax.pos
                                             in
                                          norm cfg env1 uu____15276
                                            uu____15277
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15316 =
                                            let uu____15318 = is_return body
                                               in
                                            match uu____15318 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15323;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15324;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15327 -> false  in
                                          if uu____15316
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
                                             let uu____15342 =
                                               let bv =
                                                 FStar_Syntax_Syntax.new_bv
                                                   FStar_Pervasives_Native.None
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let lb1 =
                                                 let uu____15351 =
                                                   let uu____15354 =
                                                     let uu____15365 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         x.FStar_Syntax_Syntax.sort
                                                        in
                                                     [uu____15365]  in
                                                   FStar_Syntax_Util.mk_app
                                                     repr uu____15354
                                                    in
                                                 let uu____15390 =
                                                   let uu____15391 =
                                                     FStar_TypeChecker_Env.is_total_effect
                                                       cfg.FStar_TypeChecker_Cfg.tcenv
                                                       eff_name
                                                      in
                                                   if uu____15391
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
                                                     = uu____15351;
                                                   FStar_Syntax_Syntax.lbeff
                                                     = uu____15390;
                                                   FStar_Syntax_Syntax.lbdef
                                                     = head;
                                                   FStar_Syntax_Syntax.lbattrs
                                                     = [];
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (head.FStar_Syntax_Syntax.pos)
                                                 }  in
                                               let uu____15398 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   bv
                                                  in
                                               (lb1, bv, uu____15398)  in
                                             match uu____15342 with
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
                                                   let uu____15415 =
                                                     let uu____15422 =
                                                       let uu____15423 =
                                                         let uu____15442 =
                                                           let uu____15451 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x
                                                              in
                                                           [uu____15451]  in
                                                         (uu____15442, body1,
                                                           (FStar_Pervasives_Native.Some
                                                              body_rc))
                                                          in
                                                       FStar_Syntax_Syntax.Tm_abs
                                                         uu____15423
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15422
                                                      in
                                                   uu____15415
                                                     FStar_Pervasives_Native.None
                                                     body1.FStar_Syntax_Syntax.pos
                                                    in
                                                 let close =
                                                   closure_as_term cfg env1
                                                    in
                                                 let bind_inst =
                                                   let uu____15490 =
                                                     let uu____15491 =
                                                       FStar_Syntax_Subst.compress
                                                         bind_repr
                                                        in
                                                     uu____15491.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____15490 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (bind,uu____15497::uu____15498::[])
                                                       ->
                                                       let uu____15503 =
                                                         let uu____15510 =
                                                           let uu____15511 =
                                                             let uu____15518
                                                               =
                                                               let uu____15519
                                                                 =
                                                                 let uu____15520
                                                                   =
                                                                   close
                                                                    lb.FStar_Syntax_Syntax.lbtyp
                                                                    in
                                                                 (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                                   uu____15520
                                                                  in
                                                               let uu____15521
                                                                 =
                                                                 let uu____15524
                                                                   =
                                                                   let uu____15525
                                                                    = 
                                                                    close t
                                                                     in
                                                                   (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                    cfg.FStar_TypeChecker_Cfg.tcenv
                                                                    uu____15525
                                                                    in
                                                                 [uu____15524]
                                                                  in
                                                               uu____15519 ::
                                                                 uu____15521
                                                                in
                                                             (bind,
                                                               uu____15518)
                                                              in
                                                           FStar_Syntax_Syntax.Tm_uinst
                                                             uu____15511
                                                            in
                                                         FStar_Syntax_Syntax.mk
                                                           uu____15510
                                                          in
                                                       uu____15503
                                                         FStar_Pervasives_Native.None
                                                         rng
                                                   | uu____15528 ->
                                                       failwith
                                                         "NIY : Reification of indexed effects"
                                                    in
                                                 let maybe_range_arg =
                                                   let uu____15543 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____15543
                                                   then
                                                     let uu____15556 =
                                                       let uu____15565 =
                                                         FStar_TypeChecker_Cfg.embed_simple
                                                           FStar_Syntax_Embeddings.e_range
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                          in
                                                       FStar_Syntax_Syntax.as_arg
                                                         uu____15565
                                                        in
                                                     let uu____15566 =
                                                       let uu____15577 =
                                                         let uu____15586 =
                                                           FStar_TypeChecker_Cfg.embed_simple
                                                             FStar_Syntax_Embeddings.e_range
                                                             body2.FStar_Syntax_Syntax.pos
                                                             body2.FStar_Syntax_Syntax.pos
                                                            in
                                                         FStar_Syntax_Syntax.as_arg
                                                           uu____15586
                                                          in
                                                       [uu____15577]  in
                                                     uu____15556 ::
                                                       uu____15566
                                                   else []  in
                                                 let reified =
                                                   let args =
                                                     let uu____15635 =
                                                       FStar_Syntax_Util.is_layered
                                                         ed
                                                        in
                                                     if uu____15635
                                                     then
                                                       let unit_args =
                                                         let uu____15659 =
                                                           let uu____15660 =
                                                             let uu____15663
                                                               =
                                                               let uu____15664
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15664
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15663
                                                               FStar_Syntax_Subst.compress
                                                              in
                                                           uu____15660.FStar_Syntax_Syntax.n
                                                            in
                                                         match uu____15659
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_arrow
                                                             (uu____15705::uu____15706::bs,uu____15708)
                                                             when
                                                             (FStar_List.length
                                                                bs)
                                                               >=
                                                               (Prims.of_int (2))
                                                             ->
                                                             let uu____15760
                                                               =
                                                               let uu____15769
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   bs
                                                                   (FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2))))
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15769
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15760
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____15900
                                                                     ->
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.unit_const))
                                                         | uu____15907 ->
                                                             let uu____15908
                                                               =
                                                               let uu____15914
                                                                 =
                                                                 let uu____15916
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    ed.FStar_Syntax_Syntax.mname
                                                                    in
                                                                 let uu____15918
                                                                   =
                                                                   let uu____15920
                                                                    =
                                                                    let uu____15921
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    ed
                                                                    FStar_Syntax_Util.get_bind_vc_combinator
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15921
                                                                    FStar_Pervasives_Native.snd
                                                                     in
                                                                   FStar_All.pipe_right
                                                                    uu____15920
                                                                    FStar_Syntax_Print.term_to_string
                                                                    in
                                                                 FStar_Util.format2
                                                                   "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                                   uu____15916
                                                                   uu____15918
                                                                  in
                                                               (FStar_Errors.Fatal_UnexpectedEffect,
                                                                 uu____15914)
                                                                in
                                                             FStar_Errors.raise_error
                                                               uu____15908
                                                               rng
                                                          in
                                                       let uu____15955 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let uu____15964 =
                                                         let uu____15975 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t
                                                            in
                                                         let uu____15984 =
                                                           let uu____15995 =
                                                             let uu____16006
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head1
                                                                in
                                                             let uu____16015
                                                               =
                                                               let uu____16026
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   body2
                                                                  in
                                                               [uu____16026]
                                                                in
                                                             uu____16006 ::
                                                               uu____16015
                                                              in
                                                           FStar_List.append
                                                             unit_args
                                                             uu____15995
                                                            in
                                                         uu____15975 ::
                                                           uu____15984
                                                          in
                                                       uu____15955 ::
                                                         uu____15964
                                                     else
                                                       (let uu____16085 =
                                                          let uu____16096 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              lb.FStar_Syntax_Syntax.lbtyp
                                                             in
                                                          let uu____16105 =
                                                            let uu____16116 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t
                                                               in
                                                            [uu____16116]  in
                                                          uu____16096 ::
                                                            uu____16105
                                                           in
                                                        let uu____16149 =
                                                          let uu____16160 =
                                                            let uu____16171 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            let uu____16180 =
                                                              let uu____16191
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  head1
                                                                 in
                                                              let uu____16200
                                                                =
                                                                let uu____16211
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.tun
                                                                   in
                                                                let uu____16220
                                                                  =
                                                                  let uu____16231
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    body2  in
                                                                  [uu____16231]
                                                                   in
                                                                uu____16211
                                                                  ::
                                                                  uu____16220
                                                                 in
                                                              uu____16191 ::
                                                                uu____16200
                                                               in
                                                            uu____16171 ::
                                                              uu____16180
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____16160
                                                           in
                                                        FStar_List.append
                                                          uu____16085
                                                          uu____16149)
                                                      in
                                                   let uu____16296 =
                                                     let uu____16303 =
                                                       let uu____16304 =
                                                         let uu____16318 =
                                                           let uu____16321 =
                                                             let uu____16328
                                                               =
                                                               let uu____16329
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   head_bv
                                                                  in
                                                               [uu____16329]
                                                                in
                                                             FStar_Syntax_Subst.close
                                                               uu____16328
                                                              in
                                                           let uu____16348 =
                                                             FStar_Syntax_Syntax.mk
                                                               (FStar_Syntax_Syntax.Tm_app
                                                                  (bind_inst,
                                                                    args))
                                                               FStar_Pervasives_Native.None
                                                               rng
                                                              in
                                                           FStar_All.pipe_left
                                                             uu____16321
                                                             uu____16348
                                                            in
                                                         ((false, [lb_head]),
                                                           uu____16318)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_let
                                                         uu____16304
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____16303
                                                      in
                                                   uu____16296
                                                     FStar_Pervasives_Native.None
                                                     rng
                                                    in
                                                 (FStar_TypeChecker_Cfg.log
                                                    cfg
                                                    (fun uu____16380  ->
                                                       let uu____16381 =
                                                         FStar_Syntax_Print.term_to_string
                                                           top0
                                                          in
                                                       let uu____16383 =
                                                         FStar_Syntax_Print.term_to_string
                                                           reified
                                                          in
                                                       FStar_Util.print2
                                                         "Reified (1) <%s> to %s\n"
                                                         uu____16381
                                                         uu____16383);
                                                  (let uu____16386 =
                                                     FStar_List.tl stack1  in
                                                   norm cfg env1 uu____16386
                                                     reified)))))))
                  | FStar_Syntax_Syntax.Tm_app (head,args) ->
                      ((let uu____16414 = FStar_Options.defensive ()  in
                        if uu____16414
                        then
                          let is_arg_impure uu____16429 =
                            match uu____16429 with
                            | (e,q) ->
                                let uu____16443 =
                                  let uu____16444 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16444.FStar_Syntax_Syntax.n  in
                                (match uu____16443 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____16460 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____16460
                                 | uu____16462 -> false)
                             in
                          let uu____16464 =
                            let uu____16466 =
                              let uu____16477 =
                                FStar_Syntax_Syntax.as_arg head  in
                              uu____16477 :: args  in
                            FStar_Util.for_some is_arg_impure uu____16466  in
                          (if uu____16464
                           then
                             let uu____16503 =
                               let uu____16509 =
                                 let uu____16511 =
                                   FStar_Syntax_Print.term_to_string top2  in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____16511
                                  in
                               (FStar_Errors.Warning_Defensive, uu____16509)
                                in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu____16503
                           else ())
                        else ());
                       (let fallback1 uu____16524 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16528  ->
                               let uu____16529 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____16529 "");
                          (let uu____16533 = FStar_List.tl stack1  in
                           let uu____16534 = FStar_Syntax_Util.mk_reify top2
                              in
                           norm cfg env1 uu____16533 uu____16534)
                           in
                        let fallback2 uu____16540 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16544  ->
                               let uu____16545 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____16545 "");
                          (let uu____16549 = FStar_List.tl stack1  in
                           let uu____16550 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env1 uu____16549 uu____16550)
                           in
                        let uu____16555 =
                          let uu____16556 = FStar_Syntax_Util.un_uinst head
                             in
                          uu____16556.FStar_Syntax_Syntax.n  in
                        match uu____16555 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____16562 =
                              let uu____16564 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____16564  in
                            if uu____16562
                            then fallback1 ()
                            else
                              (let uu____16569 =
                                 let uu____16571 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____16571  in
                               if uu____16569
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____16588 =
                                      let uu____16593 =
                                        FStar_Syntax_Util.mk_reify head  in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____16593 args
                                       in
                                    uu____16588 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____16594 = FStar_List.tl stack1  in
                                  norm cfg env1 uu____16594 t1))
                        | uu____16595 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____16597) ->
                      do_reify_monadic fallback cfg env1 stack1 e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____16621 = closure_as_term cfg env1 t'  in
                        reify_lift cfg e msrc mtgt uu____16621  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____16625  ->
                            let uu____16626 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____16626);
                       (let uu____16629 = FStar_List.tl stack1  in
                        norm cfg env1 uu____16629 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches1) ->
                      let branches2 =
                        FStar_All.pipe_right branches1
                          (FStar_List.map
                             (fun uu____16750  ->
                                match uu____16750 with
                                | (pat,wopt,tm) ->
                                    let uu____16798 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16798)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches2))
                          top2.FStar_Syntax_Syntax.pos
                         in
                      let uu____16830 = FStar_List.tl stack1  in
                      norm cfg env1 uu____16830 tm
                  | uu____16831 -> fallback ()))

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
              (fun uu____16845  ->
                 let uu____16846 = FStar_Ident.string_of_lid msrc  in
                 let uu____16848 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16850 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16846
                   uu____16848 uu____16850);
            (let uu____16853 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16856 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env1)
                     in
                  Prims.op_Negation uu____16856)
                in
             if uu____16853
             then
               let ed =
                 let uu____16861 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env1 uu____16861  in
               let uu____16862 =
                 let uu____16871 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 FStar_All.pipe_right uu____16871 FStar_Util.must  in
               match uu____16862 with
               | (uu____16918,repr) ->
                   let uu____16928 =
                     let uu____16937 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr
                        in
                     FStar_All.pipe_right uu____16937 FStar_Util.must  in
                   (match uu____16928 with
                    | (uu____16984,return_repr) ->
                        let return_inst =
                          let uu____16997 =
                            let uu____16998 =
                              FStar_Syntax_Subst.compress return_repr  in
                            uu____16998.FStar_Syntax_Syntax.n  in
                          match uu____16997 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm,uu____17004::[]) ->
                              let uu____17009 =
                                let uu____17016 =
                                  let uu____17017 =
                                    let uu____17024 =
                                      let uu____17025 =
                                        env1.FStar_TypeChecker_Env.universe_of
                                          env1 t
                                         in
                                      [uu____17025]  in
                                    (return_tm, uu____17024)  in
                                  FStar_Syntax_Syntax.Tm_uinst uu____17017
                                   in
                                FStar_Syntax_Syntax.mk uu____17016  in
                              uu____17009 FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                          | uu____17028 ->
                              failwith "NIY : Reification of indexed effects"
                           in
                        let uu____17032 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t
                             in
                          let lb =
                            let uu____17043 =
                              let uu____17046 =
                                let uu____17057 =
                                  FStar_Syntax_Syntax.as_arg t  in
                                [uu____17057]  in
                              FStar_Syntax_Util.mk_app repr uu____17046  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Util.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu____17043;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            }  in
                          let uu____17084 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (lb, bv, uu____17084)  in
                        (match uu____17032 with
                         | (lb_e,e_bv,e1) ->
                             let uu____17096 =
                               let uu____17103 =
                                 let uu____17104 =
                                   let uu____17118 =
                                     let uu____17121 =
                                       let uu____17128 =
                                         let uu____17129 =
                                           FStar_Syntax_Syntax.mk_binder e_bv
                                            in
                                         [uu____17129]  in
                                       FStar_Syntax_Subst.close uu____17128
                                        in
                                     let uu____17148 =
                                       let uu____17149 =
                                         let uu____17156 =
                                           let uu____17157 =
                                             let uu____17174 =
                                               let uu____17185 =
                                                 FStar_Syntax_Syntax.as_arg t
                                                  in
                                               let uu____17194 =
                                                 let uu____17205 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     e1
                                                    in
                                                 [uu____17205]  in
                                               uu____17185 :: uu____17194  in
                                             (return_inst, uu____17174)  in
                                           FStar_Syntax_Syntax.Tm_app
                                             uu____17157
                                            in
                                         FStar_Syntax_Syntax.mk uu____17156
                                          in
                                       uu____17149
                                         FStar_Pervasives_Native.None
                                         e1.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_All.pipe_left uu____17121
                                       uu____17148
                                      in
                                   ((false, [lb_e]), uu____17118)  in
                                 FStar_Syntax_Syntax.Tm_let uu____17104  in
                               FStar_Syntax_Syntax.mk uu____17103  in
                             uu____17096 FStar_Pervasives_Native.None
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu____17267 =
                  FStar_TypeChecker_Env.monad_leq env1 msrc mtgt  in
                match uu____17267 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17270 =
                      let uu____17272 = FStar_Ident.string_of_lid msrc  in
                      let uu____17274 = FStar_Ident.string_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17272 uu____17274
                       in
                    failwith uu____17270
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17277;
                      FStar_TypeChecker_Env.mtarget = uu____17278;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17279;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17299 =
                      let uu____17301 = FStar_Ident.string_of_lid msrc  in
                      let uu____17303 = FStar_Ident.string_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17301 uu____17303
                       in
                    failwith uu____17299
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17306;
                      FStar_TypeChecker_Env.mtarget = uu____17307;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17308;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____17339 =
                        FStar_TypeChecker_Env.is_reifiable_effect env1 msrc
                         in
                      if uu____17339
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____17344 =
                           let uu____17351 =
                             let uu____17352 =
                               let uu____17371 =
                                 let uu____17380 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____17380]  in
                               (uu____17371, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____17352  in
                           FStar_Syntax_Syntax.mk uu____17351  in
                         uu____17344 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____17413 =
                      env1.FStar_TypeChecker_Env.universe_of env1 t  in
                    lift uu____17413 t e1))

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
                (fun uu____17483  ->
                   match uu____17483 with
                   | (a,imp) ->
                       let uu____17502 = norm cfg env1 [] a  in
                       (uu____17502, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env1  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17512  ->
             let uu____17513 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17515 =
               FStar_Util.string_of_int (FStar_List.length env1)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17513 uu____17515);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env1 [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17541 = norm_universe cfg env1 u  in
                   FStar_All.pipe_left
                     (fun uu____17544  ->
                        FStar_Pervasives_Native.Some uu____17544) uu____17541
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2115_17545 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2115_17545.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2115_17545.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env1 [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17567 = norm_universe cfg env1 u  in
                   FStar_All.pipe_left
                     (fun uu____17570  ->
                        FStar_Pervasives_Native.Some uu____17570) uu____17567
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2126_17571 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2126_17571.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2126_17571.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17616  ->
                      match uu____17616 with
                      | (a,i) ->
                          let uu____17636 = norm cfg env1 [] a  in
                          (uu____17636, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17658  ->
                       match uu___14_17658 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17662 = norm cfg env1 [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17662
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env1)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env1 [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2143_17670 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2145_17673 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2145_17673.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2143_17670.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2143_17670.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env1  ->
      fun b  ->
        let uu____17677 = b  in
        match uu____17677 with
        | (x,imp) ->
            let x1 =
              let uu___2153_17685 = x  in
              let uu____17686 = norm cfg env1 [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2153_17685.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2153_17685.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17686
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____17697 =
                    let uu____17698 = closure_as_term cfg env1 t  in
                    FStar_Syntax_Syntax.Meta uu____17698  in
                  FStar_Pervasives_Native.Some uu____17697
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env1  ->
      fun bs  ->
        let uu____17709 =
          FStar_List.fold_left
            (fun uu____17743  ->
               fun b  ->
                 match uu____17743 with
                 | (nbs',env2) ->
                     let b1 = norm_binder cfg env2 b  in
                     ((b1 :: nbs'), (dummy :: env2))) ([], env1) bs
           in
        match uu____17709 with | (nbs,uu____17823) -> FStar_List.rev nbs

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
            let uu____17855 =
              let uu___2178_17856 = rc  in
              let uu____17857 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env1 [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2178_17856.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17857;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2178_17856.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17855
        | uu____17875 -> lopt

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
            (let uu____17885 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17887 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17885 uu____17887)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_17899  ->
      match uu___15_17899 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17912 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17912 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17916 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____17916)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun tm  ->
          let tm1 =
            let uu____17924 = norm_cb cfg  in
            reduce_primops uu____17924 cfg env1 tm  in
          let uu____17929 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17929
          then tm1
          else
            (let w t =
               let uu___2207_17948 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2207_17948.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2207_17948.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17960 =
                 let uu____17961 = FStar_Syntax_Util.unmeta t  in
                 uu____17961.FStar_Syntax_Syntax.n  in
               match uu____17960 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17973 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18037)::args1,(bv,uu____18040)::bs1) ->
                   let uu____18094 =
                     let uu____18095 = FStar_Syntax_Subst.compress t  in
                     uu____18095.FStar_Syntax_Syntax.n  in
                   (match uu____18094 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18100 -> false)
               | ([],[]) -> true
               | (uu____18131,uu____18132) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18183 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18185 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18183
                    uu____18185)
               else ();
               (let uu____18190 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18190 with
                | (hd,args) ->
                    let uu____18229 =
                      let uu____18230 = FStar_Syntax_Subst.compress hd  in
                      uu____18230.FStar_Syntax_Syntax.n  in
                    (match uu____18229 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____18238 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18240 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18242 =
                               FStar_Syntax_Print.term_to_string hd  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18238 uu____18240 uu____18242)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18247 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18265 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18267 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18265
                    uu____18267)
               else ();
               (let uu____18272 = FStar_Syntax_Util.is_squash t  in
                match uu____18272 with
                | FStar_Pervasives_Native.Some (uu____18283,t') ->
                    is_applied bs t'
                | uu____18295 ->
                    let uu____18304 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18304 with
                     | FStar_Pervasives_Native.Some (uu____18315,t') ->
                         is_applied bs t'
                     | uu____18327 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18351 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18351 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18358)::(q,uu____18360)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18403 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18405 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18403 uu____18405)
                    else ();
                    (let uu____18410 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18410 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18415 =
                           let uu____18416 = FStar_Syntax_Subst.compress p
                              in
                           uu____18416.FStar_Syntax_Syntax.n  in
                         (match uu____18415 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18427 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18427))
                          | uu____18430 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18433)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18458 =
                           let uu____18459 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18459.FStar_Syntax_Syntax.n  in
                         (match uu____18458 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18470 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18470))
                          | uu____18473 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18477 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18477 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18482 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18482 with
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
                                     let uu____18496 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18496))
                               | uu____18499 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18504)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18529 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18529 with
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
                                     let uu____18543 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18543))
                               | uu____18546 -> FStar_Pervasives_Native.None)
                          | uu____18549 -> FStar_Pervasives_Native.None)
                     | uu____18552 -> FStar_Pervasives_Native.None))
               | uu____18555 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18568 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18568 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18574)::[],uu____18575,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18595 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18597 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18595
                         uu____18597)
                    else ();
                    is_quantified_const bv phi')
               | uu____18602 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18617 =
                 let uu____18618 = FStar_Syntax_Subst.compress phi  in
                 uu____18618.FStar_Syntax_Syntax.n  in
               match uu____18617 with
               | FStar_Syntax_Syntax.Tm_match (uu____18624,br::brs) ->
                   let uu____18691 = br  in
                   (match uu____18691 with
                    | (uu____18709,uu____18710,e) ->
                        let r =
                          let uu____18732 = simp_t e  in
                          match uu____18732 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18744 =
                                FStar_List.for_all
                                  (fun uu____18763  ->
                                     match uu____18763 with
                                     | (uu____18777,uu____18778,e') ->
                                         let uu____18792 = simp_t e'  in
                                         uu____18792 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18744
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18808 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18818 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18818
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18856 =
                 match uu____18856 with
                 | (t1,q) ->
                     let uu____18877 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18877 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18909 -> (t1, q))
                  in
               let uu____18922 = FStar_Syntax_Util.head_and_args t  in
               match uu____18922 with
               | (head,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____19002 =
                 let uu____19003 = FStar_Syntax_Util.unmeta ty  in
                 uu____19003.FStar_Syntax_Syntax.n  in
               match uu____19002 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____19008) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____19013,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____19037 -> false  in
             let simplify arg =
               let uu____19070 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____19070, arg)  in
             let uu____19085 = is_forall_const tm1  in
             match uu____19085 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____19091 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____19093 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____19091
                       uu____19093)
                  else ();
                  (let uu____19098 = norm cfg env1 [] tm'  in
                   maybe_simplify_aux cfg env1 stack1 uu____19098))
             | FStar_Pervasives_Native.None  ->
                 let uu____19099 =
                   let uu____19100 = FStar_Syntax_Subst.compress tm1  in
                   uu____19100.FStar_Syntax_Syntax.n  in
                 (match uu____19099 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19104;
                              FStar_Syntax_Syntax.vars = uu____19105;_},uu____19106);
                         FStar_Syntax_Syntax.pos = uu____19107;
                         FStar_Syntax_Syntax.vars = uu____19108;_},args)
                      ->
                      let uu____19138 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19138
                      then
                        let uu____19141 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        (match uu____19141 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19199)::
                             (uu____19200,(arg,uu____19202))::[] ->
                             maybe_auto_squash arg
                         | (uu____19275,(arg,uu____19277))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19278)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19351)::uu____19352::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19422::(FStar_Pervasives_Native.Some (false
                                         ),uu____19423)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19493 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19511 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19511
                         then
                           let uu____19514 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify)
                              in
                           match uu____19514 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19572)::uu____19573::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19643::(FStar_Pervasives_Native.Some (true
                                           ),uu____19644)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19714)::(uu____19715,(arg,uu____19717))::[]
                               -> maybe_auto_squash arg
                           | (uu____19790,(arg,uu____19792))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19793)::[]
                               -> maybe_auto_squash arg
                           | uu____19866 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19884 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19884
                            then
                              let uu____19887 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify)
                                 in
                              match uu____19887 with
                              | uu____19945::(FStar_Pervasives_Native.Some
                                              (true ),uu____19946)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20016)::uu____20017::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20087)::(uu____20088,(arg,uu____20090))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20163,(p,uu____20165))::(uu____20166,
                                                                (q,uu____20168))::[]
                                  ->
                                  let uu____20240 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20240
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20245 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20263 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20263
                               then
                                 let uu____20266 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify)
                                    in
                                 match uu____20266 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20324)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20325)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20399)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20400)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20474)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20475)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20549)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20550)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20624,(arg,uu____20626))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20627)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20700)::(uu____20701,(arg,uu____20703))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20776,(arg,uu____20778))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20779)::[]
                                     ->
                                     let uu____20852 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20852
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20853)::(uu____20854,(arg,uu____20856))::[]
                                     ->
                                     let uu____20929 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20929
                                 | (uu____20930,(p,uu____20932))::(uu____20933,
                                                                   (q,uu____20935))::[]
                                     ->
                                     let uu____21007 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21007
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21012 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21030 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21030
                                  then
                                    let uu____21033 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify)
                                       in
                                    match uu____21033 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21091)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21135)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21179 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21197 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21197
                                     then
                                       match args with
                                       | (t,uu____21201)::[] ->
                                           let uu____21226 =
                                             let uu____21227 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21227.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21226 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21230::[],body,uu____21232)
                                                ->
                                                let uu____21267 = simp_t body
                                                   in
                                                (match uu____21267 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21273 -> tm1)
                                            | uu____21277 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21279))::(t,uu____21281)::[]
                                           ->
                                           let uu____21321 =
                                             let uu____21322 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21322.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21321 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21325::[],body,uu____21327)
                                                ->
                                                let uu____21362 = simp_t body
                                                   in
                                                (match uu____21362 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21370 -> tm1)
                                            | uu____21374 -> tm1)
                                       | uu____21375 -> tm1
                                     else
                                       (let uu____21388 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21388
                                        then
                                          match args with
                                          | (t,uu____21392)::[] ->
                                              let uu____21417 =
                                                let uu____21418 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21418.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21417 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21421::[],body,uu____21423)
                                                   ->
                                                   let uu____21458 =
                                                     simp_t body  in
                                                   (match uu____21458 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21464 -> tm1)
                                               | uu____21468 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21470))::(t,uu____21472)::[]
                                              ->
                                              let uu____21512 =
                                                let uu____21513 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21513.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21512 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21516::[],body,uu____21518)
                                                   ->
                                                   let uu____21553 =
                                                     simp_t body  in
                                                   (match uu____21553 with
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
                                                    | uu____21561 -> tm1)
                                               | uu____21565 -> tm1)
                                          | uu____21566 -> tm1
                                        else
                                          (let uu____21579 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21579
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21582;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21583;_},uu____21584)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21610;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21611;_},uu____21612)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21638 -> tm1
                                           else
                                             (let uu____21651 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____21651
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____21665 =
                                                    let uu____21666 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____21666.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____21665 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21677 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21691 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____21691
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____21730 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____21730
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21736 =
                                                         let uu____21737 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____21737.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____21736 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21740 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____21748 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____21748
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21757
                                                                  =
                                                                  let uu____21758
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____21758.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____21757
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,uu____21764)
                                                                    -> hd
                                                                | uu____21789
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____21793
                                                                =
                                                                let uu____21804
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____21804]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21793)
                                                       | uu____21837 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21842 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____21842 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21862 ->
                                                     let uu____21871 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____21871 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21877;
                         FStar_Syntax_Syntax.vars = uu____21878;_},args)
                      ->
                      let uu____21904 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21904
                      then
                        let uu____21907 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        (match uu____21907 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21965)::
                             (uu____21966,(arg,uu____21968))::[] ->
                             maybe_auto_squash arg
                         | (uu____22041,(arg,uu____22043))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22044)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22117)::uu____22118::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22188::(FStar_Pervasives_Native.Some (false
                                         ),uu____22189)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22259 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22277 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22277
                         then
                           let uu____22280 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify)
                              in
                           match uu____22280 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22338)::uu____22339::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22409::(FStar_Pervasives_Native.Some (true
                                           ),uu____22410)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22480)::(uu____22481,(arg,uu____22483))::[]
                               -> maybe_auto_squash arg
                           | (uu____22556,(arg,uu____22558))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22559)::[]
                               -> maybe_auto_squash arg
                           | uu____22632 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22650 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22650
                            then
                              let uu____22653 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify)
                                 in
                              match uu____22653 with
                              | uu____22711::(FStar_Pervasives_Native.Some
                                              (true ),uu____22712)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22782)::uu____22783::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22853)::(uu____22854,(arg,uu____22856))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22929,(p,uu____22931))::(uu____22932,
                                                                (q,uu____22934))::[]
                                  ->
                                  let uu____23006 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23006
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23011 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23029 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23029
                               then
                                 let uu____23032 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify)
                                    in
                                 match uu____23032 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23090)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23091)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23165)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23166)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23240)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23241)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23315)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23316)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23390,(arg,uu____23392))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23393)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23466)::(uu____23467,(arg,uu____23469))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23542,(arg,uu____23544))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23545)::[]
                                     ->
                                     let uu____23618 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23618
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23619)::(uu____23620,(arg,uu____23622))::[]
                                     ->
                                     let uu____23695 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23695
                                 | (uu____23696,(p,uu____23698))::(uu____23699,
                                                                   (q,uu____23701))::[]
                                     ->
                                     let uu____23773 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23773
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23778 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23796 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23796
                                  then
                                    let uu____23799 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify)
                                       in
                                    match uu____23799 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23857)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23901)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23945 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23963 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23963
                                     then
                                       match args with
                                       | (t,uu____23967)::[] ->
                                           let uu____23992 =
                                             let uu____23993 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23993.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23992 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23996::[],body,uu____23998)
                                                ->
                                                let uu____24033 = simp_t body
                                                   in
                                                (match uu____24033 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24039 -> tm1)
                                            | uu____24043 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24045))::(t,uu____24047)::[]
                                           ->
                                           let uu____24087 =
                                             let uu____24088 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24088.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24087 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24091::[],body,uu____24093)
                                                ->
                                                let uu____24128 = simp_t body
                                                   in
                                                (match uu____24128 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24136 -> tm1)
                                            | uu____24140 -> tm1)
                                       | uu____24141 -> tm1
                                     else
                                       (let uu____24154 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24154
                                        then
                                          match args with
                                          | (t,uu____24158)::[] ->
                                              let uu____24183 =
                                                let uu____24184 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24184.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24183 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24187::[],body,uu____24189)
                                                   ->
                                                   let uu____24224 =
                                                     simp_t body  in
                                                   (match uu____24224 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24230 -> tm1)
                                               | uu____24234 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24236))::(t,uu____24238)::[]
                                              ->
                                              let uu____24278 =
                                                let uu____24279 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24279.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24278 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24282::[],body,uu____24284)
                                                   ->
                                                   let uu____24319 =
                                                     simp_t body  in
                                                   (match uu____24319 with
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
                                                    | uu____24327 -> tm1)
                                               | uu____24331 -> tm1)
                                          | uu____24332 -> tm1
                                        else
                                          (let uu____24345 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24345
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24348;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24349;_},uu____24350)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24376;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24377;_},uu____24378)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24404 -> tm1
                                           else
                                             (let uu____24417 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____24417
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____24431 =
                                                    let uu____24432 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____24432.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____24431 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____24443 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24457 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____24457
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____24492 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____24492
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24498 =
                                                         let uu____24499 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____24499.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____24498 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24502 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24510 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24510
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24519
                                                                  =
                                                                  let uu____24520
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24520.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24519
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,uu____24526)
                                                                    -> hd
                                                                | uu____24551
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____24555
                                                                =
                                                                let uu____24566
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____24566]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24555)
                                                       | uu____24599 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24604 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____24604 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24624 ->
                                                     let uu____24633 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____24633 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24644 = simp_t t  in
                      (match uu____24644 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24653 ->
                      let uu____24676 = is_const_match tm1  in
                      (match uu____24676 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24685 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____24695  ->
               (let uu____24697 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24699 = FStar_Syntax_Print.term_to_string t  in
                let uu____24701 =
                  FStar_Util.string_of_int (FStar_List.length env1)  in
                let uu____24709 =
                  let uu____24711 =
                    let uu____24714 = firstn (Prims.of_int (4)) stack1  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24714
                     in
                  stack_to_string uu____24711  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24697 uu____24699 uu____24701 uu____24709);
               (let uu____24739 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24739
                then
                  let uu____24743 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24743 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24750 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24752 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24754 =
                          let uu____24756 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24756
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24750
                          uu____24752 uu____24754);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____24778 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack1 with
                | (Arg uu____24786)::uu____24787 -> true
                | uu____24797 -> false)
              in
           if uu____24778
           then
             let uu____24800 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____24800 (norm cfg env1 stack1)
           else
             (let t1 = maybe_simplify cfg env1 stack1 t  in
              match stack1 with
              | [] -> t1
              | (Debug (tm,time_then))::stack2 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____24814 =
                        let uu____24816 =
                          let uu____24818 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____24818  in
                        FStar_Util.string_of_int uu____24816  in
                      let uu____24825 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____24827 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                      let uu____24829 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____24814 uu____24825 uu____24827 uu____24829)
                   else ();
                   rebuild cfg env1 stack2 t1)
              | (Cfg cfg1)::stack2 -> rebuild cfg1 env1 stack2 t1
              | (Meta (uu____24838,m,r))::stack2 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env1 stack2 t2
              | (MemoLazy r)::stack2 ->
                  (set_memo cfg r (env1, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24867  ->
                        let uu____24868 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24868);
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
                  let uu____24911 =
                    let uu___2836_24912 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2836_24912.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2836_24912.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env1 stack2 uu____24911
              | (Arg (Univ uu____24915,uu____24916,uu____24917))::uu____24918
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____24922,uu____24923))::uu____24924 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env1 stack2 t2
              | (Arg
                  (Clos (env_arg,tm,uu____24940,uu____24941),aq,r))::stack2
                  when
                  let uu____24993 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24993 ->
                  let t2 =
                    let uu____24997 =
                      let uu____25002 =
                        let uu____25003 = closure_as_term cfg env_arg tm  in
                        (uu____25003, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____25002  in
                    uu____24997 FStar_Pervasives_Native.None r  in
                  rebuild cfg env1 stack2 t2
              | (Arg (Clos (env_arg,tm,m,uu____25013),aq,r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____25068  ->
                        let uu____25069 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____25069);
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
                     (let uu____25089 = FStar_ST.op_Bang m  in
                      match uu____25089 with
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
                      | FStar_Pervasives_Native.Some (uu____25177,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack2 t2))
              | (App (env2,head,aq,r))::stack' when should_reify cfg stack1
                  ->
                  let t0 = t1  in
                  let fallback msg uu____25233 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____25238  ->
                         let uu____25239 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____25239);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env2 stack' t2)
                     in
                  let uu____25249 =
                    let uu____25250 = FStar_Syntax_Subst.compress t1  in
                    uu____25250.FStar_Syntax_Syntax.n  in
                  (match uu____25249 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env2 stack1 t2
                         m ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____25278 = closure_as_term cfg env2 ty  in
                         reify_lift cfg t2 msrc mtgt uu____25278  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____25282  ->
                             let uu____25283 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____25283);
                        (let uu____25286 = FStar_List.tl stack1  in
                         norm cfg env2 uu____25286 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____25287);
                          FStar_Syntax_Syntax.pos = uu____25288;
                          FStar_Syntax_Syntax.vars = uu____25289;_},(e,uu____25291)::[])
                       -> norm cfg env2 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____25330 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____25347 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____25347 with
                        | (hd,args) ->
                            let uu____25390 =
                              let uu____25391 = FStar_Syntax_Util.un_uinst hd
                                 in
                              uu____25391.FStar_Syntax_Syntax.n  in
                            (match uu____25390 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____25395 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____25395 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____25398;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____25399;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____25400;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____25402;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____25403;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____25404;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____25405;_}
                                      when (FStar_List.length args) = n ->
                                      norm cfg env2 stack' t1
                                  | uu____25441 -> fallback " (3)" ())
                             | uu____25445 -> fallback " (4)" ()))
                   | uu____25447 -> fallback " (2)" ())
              | (App (env2,head,aq,r))::stack2 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env2 stack2 t2
              | (CBVApp (env',head,aq,r))::stack2 ->
                  let uu____25470 =
                    let uu____25471 =
                      let uu____25472 =
                        let uu____25479 =
                          let uu____25480 =
                            let uu____25512 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env1, t1, uu____25512, false)  in
                          Clos uu____25480  in
                        (uu____25479, aq, (t1.FStar_Syntax_Syntax.pos))  in
                      Arg uu____25472  in
                    uu____25471 :: stack2  in
                  norm cfg env' uu____25470 head
              | (Match (env',branches1,cfg1,r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____25587  ->
                        let uu____25588 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____25588);
                   (let scrutinee_env = env1  in
                    let env2 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____25599 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25604  ->
                           let uu____25605 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____25607 =
                             let uu____25609 =
                               FStar_All.pipe_right branches1
                                 (FStar_List.map
                                    (fun uu____25639  ->
                                       match uu____25639 with
                                       | (p,uu____25650,uu____25651) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____25609
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____25605 uu____25607);
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
                                   (fun uu___16_25676  ->
                                      match uu___16_25676 with
                                      | FStar_TypeChecker_Env.InliningDelta 
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                           -> true
                                      | uu____25680 -> false))
                               in
                            let steps =
                              let uu___3013_25683 =
                                cfg1.FStar_TypeChecker_Cfg.steps  in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3013_25683.FStar_TypeChecker_Cfg.for_extraction)
                              }  in
                            let uu___3016_25690 = cfg1  in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3016_25690.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3016_25690.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3016_25690.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3016_25690.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3016_25690.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3016_25690.FStar_TypeChecker_Cfg.reifying)
                            })
                          in
                       let norm_or_whnf env3 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env3 t2
                         else norm cfg_exclude_zeta env3 [] t2  in
                       let rec norm_pat env3 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____25765 ->
                             (p, env3)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____25796 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25885  ->
                                       fun uu____25886  ->
                                         match (uu____25885, uu____25886)
                                         with
                                         | ((pats1,env4),(p1,b)) ->
                                             let uu____26036 =
                                               norm_pat env4 p1  in
                                             (match uu____26036 with
                                              | (p2,env5) ->
                                                  (((p2, b) :: pats1), env5)))
                                    ([], env3))
                                in
                             (match uu____25796 with
                              | (pats1,env4) ->
                                  ((let uu___3044_26206 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3044_26206.FStar_Syntax_Syntax.p)
                                    }), env4))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3048_26227 = x  in
                               let uu____26228 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3048_26227.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3048_26227.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26228
                               }  in
                             ((let uu___3051_26242 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3051_26242.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3055_26253 = x  in
                               let uu____26254 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3055_26253.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3055_26253.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26254
                               }  in
                             ((let uu___3058_26268 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3058_26268.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3064_26284 = x  in
                               let uu____26285 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3064_26284.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3064_26284.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26285
                               }  in
                             let t3 = norm_or_whnf env3 t2  in
                             ((let uu___3068_26300 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3068_26300.FStar_Syntax_Syntax.p)
                               }), env3)
                          in
                       let branches2 =
                         match env2 with
                         | [] when whnf -> branches1
                         | uu____26344 ->
                             FStar_All.pipe_right branches1
                               (FStar_List.map
                                  (fun branch  ->
                                     let uu____26374 =
                                       FStar_Syntax_Subst.open_branch branch
                                        in
                                     match uu____26374 with
                                     | (p,wopt,e) ->
                                         let uu____26394 = norm_pat env2 p
                                            in
                                         (match uu____26394 with
                                          | (p1,env3) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____26449 =
                                                      norm_or_whnf env3 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____26449
                                                 in
                                              let e1 = norm_or_whnf env3 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____26466 =
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
                         if uu____26466
                         then
                           norm
                             (let uu___3087_26473 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3089_26476 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.zeta_full =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.zeta_full);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3089_26476.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3087_26473.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3087_26473.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3087_26473.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3087_26473.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3087_26473.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3087_26473.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3087_26473.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3087_26473.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____26480 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches2)) r
                          in
                       rebuild cfg1 env2 stack2 uu____26480)
                       in
                    let rec is_cons head =
                      let uu____26506 =
                        let uu____26507 = FStar_Syntax_Subst.compress head
                           in
                        uu____26507.FStar_Syntax_Syntax.n  in
                      match uu____26506 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____26512) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____26517 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26519;
                            FStar_Syntax_Syntax.fv_delta = uu____26520;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26522;
                            FStar_Syntax_Syntax.fv_delta = uu____26523;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____26524);_}
                          -> true
                      | uu____26532 -> false  in
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
                      let uu____26701 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____26701 with
                      | (head,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____26798 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26840 ->
                                    let uu____26841 =
                                      let uu____26843 = is_cons head  in
                                      Prims.op_Negation uu____26843  in
                                    FStar_Util.Inr uu____26841)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____26872 =
                                 let uu____26873 =
                                   FStar_Syntax_Util.un_uinst head  in
                                 uu____26873.FStar_Syntax_Syntax.n  in
                               (match uu____26872 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26892 ->
                                    let uu____26893 =
                                      let uu____26895 = is_cons head  in
                                      Prims.op_Negation uu____26895  in
                                    FStar_Util.Inr uu____26893))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____26986)::rest_a,(p1,uu____26989)::rest_p)
                          ->
                          let uu____27048 = matches_pat t2 p1  in
                          (match uu____27048 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____27101 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____27224 = matches_pat scrutinee1 p1  in
                          (match uu____27224 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____27270  ->
                                     let uu____27271 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____27273 =
                                       let uu____27275 =
                                         FStar_List.map
                                           (fun uu____27287  ->
                                              match uu____27287 with
                                              | (uu____27293,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____27275
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____27271 uu____27273);
                                (let env0 = env2  in
                                 let env3 =
                                   FStar_List.fold_left
                                     (fun env3  ->
                                        fun uu____27329  ->
                                          match uu____27329 with
                                          | (bv,t2) ->
                                              let uu____27352 =
                                                let uu____27359 =
                                                  let uu____27362 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____27362
                                                   in
                                                let uu____27363 =
                                                  let uu____27364 =
                                                    let uu____27396 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____27396,
                                                      false)
                                                     in
                                                  Clos uu____27364  in
                                                (uu____27359, uu____27363)
                                                 in
                                              uu____27352 :: env3) env2 s
                                    in
                                 let uu____27489 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env3 stack2 uu____27489)))
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
            (fun uu____27522  ->
               let uu____27523 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____27523);
          (let uu____27526 = is_nbe_request s  in
           if uu____27526
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27532  ->
                   let uu____27533 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27533);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27539  ->
                   let uu____27540 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27540);
              (let uu____27543 =
                 FStar_Util.record_time (fun uu____27550  -> nbe_eval c s t)
                  in
               match uu____27543 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27559  ->
                         let uu____27560 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27562 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27560 uu____27562);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27570  ->
                   let uu____27571 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27571);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27577  ->
                   let uu____27578 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27578);
              (let uu____27581 =
                 FStar_Util.record_time (fun uu____27588  -> norm c [] [] t)
                  in
               match uu____27581 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27603  ->
                         let uu____27604 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27606 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27604 uu____27606);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27625 =
          let uu____27629 =
            let uu____27631 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____27631  in
          FStar_Pervasives_Native.Some uu____27629  in
        FStar_Profiling.profile
          (fun uu____27634  -> normalize_with_primitive_steps [] s e t)
          uu____27625 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____27656  ->
             let uu____27657 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27657);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27663  ->
             let uu____27664 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27664);
        (let uu____27667 =
           FStar_Util.record_time (fun uu____27674  -> norm_comp cfg [] c)
            in
         match uu____27667 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27689  ->
                   let uu____27690 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____27692 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27690
                     uu____27692);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env1  ->
    fun u  ->
      let uu____27706 = FStar_TypeChecker_Cfg.config [] env1  in
      norm_universe uu____27706 [] u
  
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
      let uu____27728 = normalize steps env1 t  in
      FStar_TypeChecker_Env.non_informative env1 uu____27728
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env1  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27740 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env1 t ->
          let uu___3257_27759 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3257_27759.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3257_27759.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env1
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27766 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env1 ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27766
          then
            let ct1 =
              let uu____27770 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27770 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____27777 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27777
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3267_27784 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3267_27784.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3267_27784.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3267_27784.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env1 c
                     in
                  let uu___3271_27786 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3271_27786.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3271_27786.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3271_27786.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3271_27786.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3274_27787 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3274_27787.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3274_27787.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27790 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env1  ->
    fun lc  ->
      let uu____27802 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env1 lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____27802
      then
        let uu____27805 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____27805 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3282_27809 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env1)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3282_27809.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3282_27809.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3282_27809.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env1  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3289_27828  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                   t) ()
        with
        | uu___3288_27831 ->
            ((let uu____27833 =
                let uu____27839 =
                  let uu____27841 = FStar_Util.message_of_exn uu___3288_27831
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27841
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27839)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27833);
             t)
         in
      FStar_Syntax_Print.term_to_string' env1.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env1  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3299_27860  ->
             match () with
             | () ->
                 let uu____27861 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                    in
                 norm_comp uu____27861 [] c) ()
        with
        | uu___3298_27870 ->
            ((let uu____27872 =
                let uu____27878 =
                  let uu____27880 = FStar_Util.message_of_exn uu___3298_27870
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27880
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27878)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27872);
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
                   let uu____27929 =
                     let uu____27930 =
                       let uu____27937 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27937)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27930  in
                   mk uu____27929 t01.FStar_Syntax_Syntax.pos
               | uu____27942 -> t2)
          | uu____27943 -> t2  in
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
        let uu____28037 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____28037 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____28050 ->
                 let uu____28051 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____28051 with
                  | (actuals,uu____28061,uu____28062) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____28082 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____28082 with
                         | (binders,args) ->
                             let uu____28093 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____28093
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
      | uu____28108 ->
          let uu____28109 = FStar_Syntax_Util.head_and_args t  in
          (match uu____28109 with
           | (head,args) ->
               let uu____28152 =
                 let uu____28153 = FStar_Syntax_Subst.compress head  in
                 uu____28153.FStar_Syntax_Syntax.n  in
               (match uu____28152 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____28174 =
                      let uu____28181 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____28181  in
                    (match uu____28174 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____28205 =
                              env1.FStar_TypeChecker_Env.type_of
                                (let uu___3369_28213 = env1  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3369_28213.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3369_28213.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3369_28213.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3369_28213.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3369_28213.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3369_28213.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3369_28213.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3369_28213.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3369_28213.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3369_28213.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3369_28213.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3369_28213.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3369_28213.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3369_28213.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3369_28213.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3369_28213.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3369_28213.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3369_28213.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3369_28213.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3369_28213.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3369_28213.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3369_28213.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3369_28213.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3369_28213.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3369_28213.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3369_28213.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3369_28213.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3369_28213.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3369_28213.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3369_28213.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3369_28213.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3369_28213.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3369_28213.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3369_28213.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3369_28213.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3369_28213.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3369_28213.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3369_28213.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3369_28213.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3369_28213.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3369_28213.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3369_28213.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3369_28213.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____28205 with
                            | (uu____28216,ty,uu____28218) ->
                                eta_expand_with_type env1 t ty))
                | uu____28219 ->
                    let uu____28220 =
                      env1.FStar_TypeChecker_Env.type_of
                        (let uu___3376_28228 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3376_28228.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3376_28228.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3376_28228.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3376_28228.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3376_28228.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3376_28228.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3376_28228.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3376_28228.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3376_28228.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3376_28228.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3376_28228.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3376_28228.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3376_28228.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3376_28228.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3376_28228.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3376_28228.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3376_28228.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3376_28228.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3376_28228.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3376_28228.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3376_28228.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3376_28228.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3376_28228.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3376_28228.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3376_28228.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3376_28228.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3376_28228.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3376_28228.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3376_28228.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3376_28228.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3376_28228.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3376_28228.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3376_28228.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3376_28228.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3376_28228.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3376_28228.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3376_28228.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3376_28228.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3376_28228.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3376_28228.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3376_28228.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3376_28228.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3376_28228.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____28220 with
                     | (uu____28231,ty,uu____28233) ->
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
      let uu___3388_28315 = x  in
      let uu____28316 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3388_28315.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3388_28315.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28316
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28319 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28335 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28336 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28337 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28338 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28345 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28346 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28347 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3414_28381 = rc  in
          let uu____28382 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28391 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3414_28381.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28382;
            FStar_Syntax_Syntax.residual_flags = uu____28391
          }  in
        let uu____28394 =
          let uu____28395 =
            let uu____28414 = elim_delayed_subst_binders bs  in
            let uu____28423 = elim_delayed_subst_term t2  in
            let uu____28426 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28414, uu____28423, uu____28426)  in
          FStar_Syntax_Syntax.Tm_abs uu____28395  in
        mk1 uu____28394
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28463 =
          let uu____28464 =
            let uu____28479 = elim_delayed_subst_binders bs  in
            let uu____28488 = elim_delayed_subst_comp c  in
            (uu____28479, uu____28488)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28464  in
        mk1 uu____28463
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28507 =
          let uu____28508 =
            let uu____28515 = elim_bv bv  in
            let uu____28516 = elim_delayed_subst_term phi  in
            (uu____28515, uu____28516)  in
          FStar_Syntax_Syntax.Tm_refine uu____28508  in
        mk1 uu____28507
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28547 =
          let uu____28548 =
            let uu____28565 = elim_delayed_subst_term t2  in
            let uu____28568 = elim_delayed_subst_args args  in
            (uu____28565, uu____28568)  in
          FStar_Syntax_Syntax.Tm_app uu____28548  in
        mk1 uu____28547
    | FStar_Syntax_Syntax.Tm_match (t2,branches1) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3436_28640 = p  in
              let uu____28641 =
                let uu____28642 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28642  in
              {
                FStar_Syntax_Syntax.v = uu____28641;
                FStar_Syntax_Syntax.p =
                  (uu___3436_28640.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3440_28644 = p  in
              let uu____28645 =
                let uu____28646 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28646  in
              {
                FStar_Syntax_Syntax.v = uu____28645;
                FStar_Syntax_Syntax.p =
                  (uu___3440_28644.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3446_28653 = p  in
              let uu____28654 =
                let uu____28655 =
                  let uu____28662 = elim_bv x  in
                  let uu____28663 = elim_delayed_subst_term t0  in
                  (uu____28662, uu____28663)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28655  in
              {
                FStar_Syntax_Syntax.v = uu____28654;
                FStar_Syntax_Syntax.p =
                  (uu___3446_28653.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3452_28688 = p  in
              let uu____28689 =
                let uu____28690 =
                  let uu____28704 =
                    FStar_List.map
                      (fun uu____28730  ->
                         match uu____28730 with
                         | (x,b) ->
                             let uu____28747 = elim_pat x  in
                             (uu____28747, b)) pats
                     in
                  (fv, uu____28704)  in
                FStar_Syntax_Syntax.Pat_cons uu____28690  in
              {
                FStar_Syntax_Syntax.v = uu____28689;
                FStar_Syntax_Syntax.p =
                  (uu___3452_28688.FStar_Syntax_Syntax.p)
              }
          | uu____28762 -> p  in
        let elim_branch uu____28786 =
          match uu____28786 with
          | (pat,wopt,t3) ->
              let uu____28812 = elim_pat pat  in
              let uu____28815 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28818 = elim_delayed_subst_term t3  in
              (uu____28812, uu____28815, uu____28818)
           in
        let uu____28823 =
          let uu____28824 =
            let uu____28847 = elim_delayed_subst_term t2  in
            let uu____28850 = FStar_List.map elim_branch branches1  in
            (uu____28847, uu____28850)  in
          FStar_Syntax_Syntax.Tm_match uu____28824  in
        mk1 uu____28823
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28981 =
          match uu____28981 with
          | (tc,topt) ->
              let uu____29016 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____29026 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____29026
                | FStar_Util.Inr c ->
                    let uu____29028 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____29028
                 in
              let uu____29029 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____29016, uu____29029)
           in
        let uu____29038 =
          let uu____29039 =
            let uu____29066 = elim_delayed_subst_term t2  in
            let uu____29069 = elim_ascription a  in
            (uu____29066, uu____29069, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____29039  in
        mk1 uu____29038
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3482_29132 = lb  in
          let uu____29133 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____29136 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3482_29132.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3482_29132.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____29133;
            FStar_Syntax_Syntax.lbeff =
              (uu___3482_29132.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____29136;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3482_29132.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3482_29132.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____29139 =
          let uu____29140 =
            let uu____29154 =
              let uu____29162 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____29162)  in
            let uu____29174 = elim_delayed_subst_term t2  in
            (uu____29154, uu____29174)  in
          FStar_Syntax_Syntax.Tm_let uu____29140  in
        mk1 uu____29139
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____29219 =
          let uu____29220 =
            let uu____29227 = elim_delayed_subst_term tm  in
            (uu____29227, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____29220  in
        mk1 uu____29219
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29238 =
          let uu____29239 =
            let uu____29246 = elim_delayed_subst_term t2  in
            let uu____29249 = elim_delayed_subst_meta md  in
            (uu____29246, uu____29249)  in
          FStar_Syntax_Syntax.Tm_meta uu____29239  in
        mk1 uu____29238

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29258  ->
         match uu___17_29258 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29262 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29262
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
        let uu____29285 =
          let uu____29286 =
            let uu____29295 = elim_delayed_subst_term t  in
            (uu____29295, uopt)  in
          FStar_Syntax_Syntax.Total uu____29286  in
        mk1 uu____29285
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29312 =
          let uu____29313 =
            let uu____29322 = elim_delayed_subst_term t  in
            (uu____29322, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29313  in
        mk1 uu____29312
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3515_29331 = ct  in
          let uu____29332 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29335 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29346 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3515_29331.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3515_29331.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29332;
            FStar_Syntax_Syntax.effect_args = uu____29335;
            FStar_Syntax_Syntax.flags = uu____29346
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29349  ->
    match uu___18_29349 with
    | FStar_Syntax_Syntax.Meta_pattern (names,args) ->
        let uu____29384 =
          let uu____29405 = FStar_List.map elim_delayed_subst_term names  in
          let uu____29414 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29405, uu____29414)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29384
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____29469 =
          let uu____29476 = elim_delayed_subst_term t  in (m, uu____29476)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____29469
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____29488 =
          let uu____29497 = elim_delayed_subst_term t  in
          (m1, m2, uu____29497)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29488
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
      (fun uu____29530  ->
         match uu____29530 with
         | (t,q) ->
             let uu____29549 = elim_delayed_subst_term t  in (uu____29549, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29577  ->
         match uu____29577 with
         | (x,q) ->
             let uu____29596 =
               let uu___3541_29597 = x  in
               let uu____29598 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3541_29597.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3541_29597.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29598
               }  in
             (uu____29596, q)) bs

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
            | (uu____29706,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29738,FStar_Util.Inl t) ->
                let uu____29760 =
                  let uu____29767 =
                    let uu____29768 =
                      let uu____29783 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29783)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29768  in
                  FStar_Syntax_Syntax.mk uu____29767  in
                uu____29760 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29796 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29796 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env1 t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29828 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29901 ->
                    let uu____29902 =
                      let uu____29911 =
                        let uu____29912 = FStar_Syntax_Subst.compress t4  in
                        uu____29912.FStar_Syntax_Syntax.n  in
                      (uu____29911, tc)  in
                    (match uu____29902 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29941) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29988) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____30033,FStar_Util.Inl uu____30034) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____30065 -> failwith "Impossible")
                 in
              (match uu____29828 with
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
          let uu____30204 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inl t)  in
          match uu____30204 with
          | (univ_names1,binders1,tc) ->
              let uu____30278 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30278)
  
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
          let uu____30332 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inr c)  in
          match uu____30332 with
          | (univ_names1,binders1,tc) ->
              let uu____30406 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30406)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env1  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____30448 = elim_uvars_aux_t env1 univ_names binders typ  in
          (match uu____30448 with
           | (univ_names1,binders1,typ1) ->
               let uu___3624_30488 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3624_30488.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3624_30488.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3624_30488.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3624_30488.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3624_30488.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3630_30503 = s  in
          let uu____30504 =
            let uu____30505 =
              let uu____30514 = FStar_List.map (elim_uvars env1) sigs  in
              (uu____30514, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____30505  in
          {
            FStar_Syntax_Syntax.sigel = uu____30504;
            FStar_Syntax_Syntax.sigrng =
              (uu___3630_30503.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3630_30503.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3630_30503.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3630_30503.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3630_30503.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____30533 = elim_uvars_aux_t env1 univ_names [] typ  in
          (match uu____30533 with
           | (univ_names1,uu____30557,typ1) ->
               let uu___3644_30579 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3644_30579.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3644_30579.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3644_30579.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3644_30579.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3644_30579.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____30586 = elim_uvars_aux_t env1 univ_names [] typ  in
          (match uu____30586 with
           | (univ_names1,uu____30610,typ1) ->
               let uu___3655_30632 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3655_30632.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3655_30632.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3655_30632.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3655_30632.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3655_30632.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30662 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30662 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____30687 =
                            let uu____30688 =
                              let uu____30689 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env1 uu____30689  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30688
                             in
                          elim_delayed_subst_term uu____30687  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3671_30692 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3671_30692.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3671_30692.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3671_30692.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3671_30692.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3674_30693 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3674_30693.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3674_30693.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3674_30693.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3674_30693.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3674_30693.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____30702 = elim_uvars_aux_t env1 us [] t  in
          (match uu____30702 with
           | (us1,uu____30726,t1) ->
               let uu___3685_30748 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3685_30748.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3685_30748.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3685_30748.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3685_30748.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3685_30748.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30750 =
            elim_uvars_aux_t env1 ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____30750 with
           | (univs,binders,uu____30769) ->
               let uu____30790 =
                 let uu____30795 = FStar_Syntax_Subst.univ_var_opening univs
                    in
                 match uu____30795 with
                 | (univs_opening,univs1) ->
                     let uu____30818 =
                       FStar_Syntax_Subst.univ_var_closing univs1  in
                     (univs_opening, uu____30818)
                  in
               (match uu____30790 with
                | (univs_opening,univs_closing) ->
                    let uu____30821 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30827 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30828 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30827, uu____30828)  in
                    (match uu____30821 with
                     | (b_opening,b_closing) ->
                         let n = FStar_List.length univs  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30854 =
                           match uu____30854 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30872 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30872 with
                                | (us1,t1) ->
                                    let uu____30883 =
                                      let uu____30892 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30897 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30892, uu____30897)  in
                                    (match uu____30883 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30920 =
                                           let uu____30929 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____30934 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____30929, uu____30934)  in
                                         (match uu____30920 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30958 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30958
                                                 in
                                              let uu____30959 =
                                                elim_uvars_aux_t env1 [] []
                                                  t2
                                                 in
                                              (match uu____30959 with
                                               | (uu____30986,uu____30987,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____31010 =
                                                       let uu____31011 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____31011
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____31010
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____31020 =
                             elim_uvars_aux_t env1 univs binders t  in
                           match uu____31020 with
                           | (uu____31039,uu____31040,t1) -> t1  in
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
                             | uu____31116 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____31143 =
                               let uu____31144 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____31144.FStar_Syntax_Syntax.n  in
                             match uu____31143 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____31203 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31237 =
                               let uu____31238 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31238.FStar_Syntax_Syntax.n  in
                             match uu____31237 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31261) ->
                                 let uu____31286 = destruct_action_body body
                                    in
                                 (match uu____31286 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31335 ->
                                 let uu____31336 = destruct_action_body t  in
                                 (match uu____31336 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31391 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31391 with
                           | (action_univs,t) ->
                               let uu____31400 = destruct_action_typ_templ t
                                  in
                               (match uu____31400 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3769_31447 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3769_31447.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3769_31447.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3772_31449 = ed  in
                           let uu____31450 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____31451 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____31452 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3772_31449.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3772_31449.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31450;
                             FStar_Syntax_Syntax.combinators = uu____31451;
                             FStar_Syntax_Syntax.actions = uu____31452;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3772_31449.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3775_31455 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3775_31455.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3775_31455.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3775_31455.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3775_31455.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3775_31455.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31476 =
            match uu___19_31476 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____31507 = elim_uvars_aux_t env1 us [] t  in
                (match uu____31507 with
                 | (us1,uu____31539,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3790_31570 = sub_eff  in
            let uu____31571 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____31574 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3790_31570.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3790_31570.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31571;
              FStar_Syntax_Syntax.lift = uu____31574
            }  in
          let uu___3793_31577 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3793_31577.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3793_31577.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3793_31577.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3793_31577.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3793_31577.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____31587 = elim_uvars_aux_c env1 univ_names binders comp  in
          (match uu____31587 with
           | (univ_names1,binders1,comp1) ->
               let uu___3806_31627 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3806_31627.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3806_31627.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3806_31627.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3806_31627.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3806_31627.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31630 -> s
      | FStar_Syntax_Syntax.Sig_fail uu____31631 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31644 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n,p,(us_t,t),(us_ty,ty))
          ->
          let uu____31674 = elim_uvars_aux_t env1 us_t [] t  in
          (match uu____31674 with
           | (us_t1,uu____31698,t1) ->
               let uu____31720 = elim_uvars_aux_t env1 us_ty [] ty  in
               (match uu____31720 with
                | (us_ty1,uu____31744,ty1) ->
                    let uu___3833_31766 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3833_31766.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3833_31766.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3833_31766.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3833_31766.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3833_31766.FStar_Syntax_Syntax.sigopts)
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
        let uu____31817 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env1 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____31817 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____31839 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____31839 with
             | (uu____31846,head_def) ->
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
      let uu____31852 = FStar_Syntax_Util.head_and_args t  in
      match uu____31852 with
      | (head,args) ->
          let uu____31897 =
            let uu____31898 = FStar_Syntax_Subst.compress head  in
            uu____31898.FStar_Syntax_Syntax.n  in
          (match uu____31897 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31905;
                  FStar_Syntax_Syntax.vars = uu____31906;_},us)
               -> aux fv us args
           | uu____31912 -> FStar_Pervasives_Native.None)
  