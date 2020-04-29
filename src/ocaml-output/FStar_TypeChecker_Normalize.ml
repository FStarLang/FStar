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
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5788  ->
                                        let uu____5789 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5789);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5794  ->
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
                                           (fun uu____5808  ->
                                              let uu____5809 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5809);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5817  ->
                                              let uu____5818 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5820 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5818 uu____5820);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5823 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5827  ->
                                 let uu____5828 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5828);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5834  ->
                            let uu____5835 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5835);
                       (match args with
                        | (a1,uu____5841)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5866 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5880  ->
                            let uu____5881 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5881);
                       (match args with
                        | (t,uu____5887)::(r,uu____5889)::[] ->
                            let uu____5930 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5930 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5936 -> tm))
                  | uu____5947 -> tm))
  
let reduce_equality :
  'uuuuuu5958 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5958)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___754_6007 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___756_6010 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___756_6010.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___756_6010.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___756_6010.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.zeta_full =
                    (uu___756_6010.FStar_TypeChecker_Cfg.zeta_full);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___756_6010.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___756_6010.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___756_6010.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___756_6010.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___756_6010.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___756_6010.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___756_6010.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___756_6010.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___756_6010.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___756_6010.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___756_6010.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___756_6010.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___756_6010.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___756_6010.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___756_6010.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___756_6010.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___756_6010.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___756_6010.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___756_6010.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___756_6010.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___756_6010.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___756_6010.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___754_6007.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___754_6007.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___754_6007.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___754_6007.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___754_6007.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___754_6007.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___754_6007.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____6021 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____6032 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____6043 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd  ->
    fun args  ->
      let aux min_args =
        let uu____6064 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____6064
          (fun n  ->
             if n < min_args
             then Norm_request_none
             else
               if n = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____6096 =
        let uu____6097 = FStar_Syntax_Util.un_uinst hd  in
        uu____6097.FStar_Syntax_Syntax.n  in
      match uu____6096 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu____6106 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____6115 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____6115)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd  ->
    fun args  ->
      let uu____6128 =
        let uu____6129 = FStar_Syntax_Util.un_uinst hd  in
        uu____6129.FStar_Syntax_Syntax.n  in
      match uu____6128 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6187 = FStar_Syntax_Util.mk_app hd [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____6187 rest
           | uu____6214 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6254 = FStar_Syntax_Util.mk_app hd [t]  in
               FStar_Syntax_Util.mk_app uu____6254 rest
           | uu____6273 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____6347 = FStar_Syntax_Util.mk_app hd [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____6347 rest
           | uu____6382 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6384 ->
          let uu____6385 =
            let uu____6387 = FStar_Syntax_Print.term_to_string hd  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6387
             in
          failwith uu____6385
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6408  ->
    match uu___9_6408 with
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
        let uu____6415 =
          let uu____6418 =
            let uu____6419 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6419  in
          [uu____6418]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6415
    | FStar_Syntax_Embeddings.UnfoldFully names ->
        let uu____6427 =
          let uu____6430 =
            let uu____6431 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldFully uu____6431  in
          [uu____6430]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6427
    | FStar_Syntax_Embeddings.UnfoldAttr names ->
        let uu____6439 =
          let uu____6442 =
            let uu____6443 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6443  in
          [uu____6442]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6439
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s  ->
    let s1 = FStar_List.concatMap tr_norm_step s  in
    let add_exclude s2 z =
      let uu____6479 =
        FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2  in
      if uu____6479 then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2  in
    let s2 = FStar_TypeChecker_Env.Beta :: s1  in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta  in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota  in s4
  
let get_norm_request :
  'uuuuuu6504 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu6504) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6555 =
            let uu____6560 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6560 s  in
          match uu____6555 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6576 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6576
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
        | uu____6611::(tm,uu____6613)::[] ->
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
        | (tm,uu____6642)::[] ->
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
        | (steps,uu____6663)::uu____6664::(tm,uu____6666)::[] ->
            let uu____6687 =
              let uu____6692 = full_norm steps  in parse_steps uu____6692  in
            (match uu____6687 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s), tm))
        | uu____6722 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6754 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6761  ->
                    match uu___10_6761 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6763 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6765 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6769 -> true
                    | uu____6773 -> false))
             in
          if uu____6754
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6783  ->
             let uu____6784 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6784);
        (let tm_norm =
           let uu____6788 =
             let uu____6803 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6803.FStar_TypeChecker_Env.nbe  in
           uu____6788 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6807  ->
              let uu____6808 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6808);
         tm_norm)
  
let firstn :
  'uuuuuu6818 .
    Prims.int ->
      'uuuuuu6818 Prims.list ->
        ('uuuuuu6818 Prims.list * 'uuuuuu6818 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack1  ->
      let rec drop_irrel uu___11_6875 =
        match uu___11_6875 with
        | (MemoLazy uu____6880)::s -> drop_irrel s
        | (UnivArgs uu____6890)::s -> drop_irrel s
        | s -> s  in
      let uu____6903 = drop_irrel stack1  in
      match uu____6903 with
      | (App
          (uu____6907,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6908;
                        FStar_Syntax_Syntax.vars = uu____6909;_},uu____6910,uu____6911))::uu____6912
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6917 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6946) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6956) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6977  ->
                  match uu____6977 with
                  | (a,uu____6988) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6999 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____7016 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____7018 -> false
    | FStar_Syntax_Syntax.Tm_type uu____7032 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____7034 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____7036 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____7038 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____7040 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____7043 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____7051 -> false
    | FStar_Syntax_Syntax.Tm_let uu____7059 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____7074 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____7094 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____7110 -> true
    | FStar_Syntax_Syntax.Tm_match uu____7118 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7190  ->
                   match uu____7190 with
                   | (a,uu____7201) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7212) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____7311,args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7366  ->
                        match uu____7366 with
                        | (a,uu____7377) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7386,uu____7387,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7393,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7399 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7409 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7411 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7422 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7433 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7444 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7455 -> false
  
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
            let uu____7488 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7488 with
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
              (fun uu____7687  ->
                 fun uu____7688  ->
                   match (uu____7687, uu____7688) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7794 =
            match uu____7794 with
            | (x,y,z) ->
                let uu____7814 = FStar_Util.string_of_bool x  in
                let uu____7816 = FStar_Util.string_of_bool y  in
                let uu____7818 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7814 uu____7816
                  uu____7818
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7846  ->
                    let uu____7847 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7849 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7847 uu____7849);
               if b then reif else no)
            else
              if
                (let uu____7864 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7864)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7869  ->
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
                          ((is_rec,uu____7904),uu____7905);
                        FStar_Syntax_Syntax.sigrng = uu____7906;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7908;
                        FStar_Syntax_Syntax.sigattrs = uu____7909;
                        FStar_Syntax_Syntax.sigopts = uu____7910;_},uu____7911),uu____7912),uu____7913,uu____7914,uu____7915)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8024  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____8026,uu____8027,uu____8028,uu____8029) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8096  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____8099),uu____8100);
                        FStar_Syntax_Syntax.sigrng = uu____8101;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____8103;
                        FStar_Syntax_Syntax.sigattrs = uu____8104;
                        FStar_Syntax_Syntax.sigopts = uu____8105;_},uu____8106),uu____8107),uu____8108,uu____8109,uu____8110)
                     when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8219  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8221,FStar_Pervasives_Native.Some
                    uu____8222,uu____8223,uu____8224) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8292  ->
                           let uu____8293 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8293);
                      (let uu____8296 =
                         let uu____8308 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8334 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8334
                            in
                         let uu____8346 =
                           let uu____8358 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8384 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8384
                              in
                           let uu____8400 =
                             let uu____8412 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8438 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8438
                                in
                             [uu____8412]  in
                           uu____8358 :: uu____8400  in
                         uu____8308 :: uu____8346  in
                       comb_or uu____8296))
                 | (uu____8486,uu____8487,FStar_Pervasives_Native.Some
                    uu____8488,uu____8489) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8557  ->
                           let uu____8558 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8558);
                      (let uu____8561 =
                         let uu____8573 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8599 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8599
                            in
                         let uu____8611 =
                           let uu____8623 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8649 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8649
                              in
                           let uu____8665 =
                             let uu____8677 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8703 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8703
                                in
                             [uu____8677]  in
                           uu____8623 :: uu____8665  in
                         uu____8573 :: uu____8611  in
                       comb_or uu____8561))
                 | (uu____8751,uu____8752,uu____8753,FStar_Pervasives_Native.Some
                    uu____8754) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8822  ->
                           let uu____8823 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8823);
                      (let uu____8826 =
                         let uu____8838 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8864 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8864
                            in
                         let uu____8876 =
                           let uu____8888 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8914 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8914
                              in
                           let uu____8930 =
                             let uu____8942 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8968 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8968
                                in
                             [uu____8942]  in
                           uu____8888 :: uu____8930  in
                         uu____8838 :: uu____8876  in
                       comb_or uu____8826))
                 | uu____9016 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____9062  ->
                           let uu____9063 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____9065 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____9067 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____9063 uu____9065 uu____9067);
                      (let uu____9070 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_9076  ->
                                 match uu___12_9076 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____9082 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____9082 l))
                          in
                       FStar_All.pipe_left yesno uu____9070)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____9098  ->
               let uu____9099 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____9101 =
                 let uu____9103 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____9103  in
               let uu____9104 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____9099 uu____9101 uu____9104);
          (match res with
           | (false ,uu____9107,uu____9108) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____9133 ->
               let uu____9143 =
                 let uu____9145 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9145
                  in
               FStar_All.pipe_left failwith uu____9143)
  
let decide_unfolding :
  'uuuuuu9164 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'uuuuuu9164 ->
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
                    let uu___1165_9233 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1167_9236 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1167_9236.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1167_9236.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1165_9233.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1165_9233.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1165_9233.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1165_9233.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1165_9233.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1165_9233.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1165_9233.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1165_9233.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____9298 = push e t  in (UnivArgs (us, r)) ::
                          uu____9298
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9310 =
                      let uu____9317 =
                        let uu____9318 =
                          let uu____9319 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____9319  in
                        FStar_Syntax_Syntax.Tm_constant uu____9318  in
                      FStar_Syntax_Syntax.mk uu____9317  in
                    uu____9310 FStar_Pervasives_Native.None
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
    let uu____9385 =
      let uu____9386 = FStar_Syntax_Subst.compress t  in
      uu____9386.FStar_Syntax_Syntax.n  in
    match uu____9385 with
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____9417 =
          let uu____9418 = FStar_Syntax_Util.un_uinst hd  in
          uu____9418.FStar_Syntax_Syntax.n  in
        (match uu____9417 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9435 =
                 let uu____9442 =
                   let uu____9453 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9453 FStar_List.tl  in
                 FStar_All.pipe_right uu____9442 FStar_List.hd  in
               FStar_All.pipe_right uu____9435 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9552 -> FStar_Pervasives_Native.None)
    | uu____9553 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9832 ->
                   let uu____9847 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9847
               | uu____9850 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9860  ->
               let uu____9861 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9863 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9865 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9867 =
                 FStar_Util.string_of_int (FStar_List.length env1)  in
               let uu____9875 =
                 let uu____9877 =
                   let uu____9880 = firstn (Prims.of_int (4)) stack1  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9880
                    in
                 stack_to_string uu____9877  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9861 uu____9863 uu____9865 uu____9867 uu____9875);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9908  ->
               let uu____9909 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9909);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9915  ->
                     let uu____9916 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9916);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9919 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9923  ->
                     let uu____9924 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9924);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____9927 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9931  ->
                     let uu____9932 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9932);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9935 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9939  ->
                     let uu____9940 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9940);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9943;
                 FStar_Syntax_Syntax.fv_delta = uu____9944;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9948  ->
                     let uu____9949 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9949);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9952;
                 FStar_Syntax_Syntax.fv_delta = uu____9953;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9954);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9964  ->
                     let uu____9965 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9965);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____9971 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____9971 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level uu____9974)
                    when uu____9974 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9978  ->
                          let uu____9979 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9979);
                     rebuild cfg env1 stack1 t1)
                | uu____9982 ->
                    let uu____9985 =
                      decide_unfolding cfg env1 stack1
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____9985 with
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
               let uu____10024 = closure_as_term cfg env1 t2  in
               rebuild cfg env1 stack1 uu____10024
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10052 = is_norm_request hd args  in
                  uu____10052 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____10058 = rejig_norm_request hd args  in
                 norm cfg env1 stack1 uu____10058))
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10086 = is_norm_request hd args  in
                  uu____10086 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1278_10093 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1280_10096 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1280_10096.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1278_10093.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1278_10093.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1278_10093.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1278_10093.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1278_10093.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1278_10093.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____10103 =
                   get_norm_request cfg (norm cfg' env1 []) args  in
                 match uu____10103 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack2 =
                         FStar_All.pipe_right stack1
                           (FStar_List.fold_right
                              (fun uu____10139  ->
                                 fun stack2  ->
                                   match uu____10139 with
                                   | (a,aq) ->
                                       let uu____10151 =
                                         let uu____10152 =
                                           let uu____10159 =
                                             let uu____10160 =
                                               let uu____10192 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env1, a, uu____10192, false)
                                                in
                                             Clos uu____10160  in
                                           (uu____10159, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10152  in
                                       uu____10151 :: stack2) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10260  ->
                            let uu____10261 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10261);
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
                         let uu____10293 =
                           let uu____10295 =
                             let uu____10297 = FStar_Util.time_diff start fin
                                in
                             FStar_Pervasives_Native.snd uu____10297  in
                           FStar_Util.string_of_int uu____10295  in
                         let uu____10304 =
                           FStar_Syntax_Print.term_to_string tm'  in
                         let uu____10306 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                         let uu____10308 =
                           FStar_Syntax_Print.term_to_string tm_norm  in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____10293 uu____10304 uu____10306 uu____10308)
                      else ();
                      rebuild cfg env1 stack1 tm_norm)
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     let delta_level =
                       let uu____10328 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___13_10335  ->
                                 match uu___13_10335 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____10337 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____10339 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____10343 -> true
                                 | uu____10347 -> false))
                          in
                       if uu____10328
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let cfg'1 =
                       let uu___1318_10355 = cfg  in
                       let uu____10356 =
                         let uu___1320_10357 =
                           FStar_TypeChecker_Cfg.to_fsteps s  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1320_10357.FStar_TypeChecker_Cfg.for_extraction)
                         }  in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____10356;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1318_10355.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1318_10355.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1318_10355.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1318_10355.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1318_10355.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___1318_10355.FStar_TypeChecker_Cfg.reifying)
                       }  in
                     let stack' =
                       let tail = (Cfg cfg) :: stack1  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____10365 =
                           let uu____10366 =
                             let uu____10371 = FStar_Util.now ()  in
                             (tm, uu____10371)  in
                           Debug uu____10366  in
                         uu____10365 :: tail
                       else tail  in
                     norm cfg'1 env1 stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env1 u  in
               let uu____10376 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env1 stack1 uu____10376
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env1 stack1 t'
               else
                 (let us1 =
                    let uu____10387 =
                      let uu____10394 =
                        FStar_List.map (norm_universe cfg env1) us  in
                      (uu____10394, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10387  in
                  let stack2 = us1 :: stack1  in norm cfg env1 stack2 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10403 = lookup_bvar env1 x  in
               (match uu____10403 with
                | Univ uu____10404 ->
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
                      let uu____10458 = FStar_ST.op_Bang r  in
                      (match uu____10458 with
                       | FStar_Pervasives_Native.Some (env3,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10554  ->
                                 let uu____10555 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10557 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10555
                                   uu____10557);
                            (let uu____10560 = maybe_weakly_reduced t'  in
                             if uu____10560
                             then
                               match stack1 with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env3 stack1 t'
                               | uu____10563 -> norm cfg env3 stack1 t'
                             else rebuild cfg env3 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env2 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env2 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____10607)::uu____10608 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10619,uu____10620))::stack_rest ->
                    (match c with
                     | Univ uu____10624 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env1)
                           stack_rest t1
                     | uu____10633 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10663  ->
                                    let uu____10664 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10664);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env1) stack_rest body)
                          | b::tl ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10700  ->
                                    let uu____10701 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10701);
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
                       (fun uu____10749  ->
                          let uu____10750 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10750);
                     norm cfg env1 stack2 t1)
                | (Match uu____10753)::uu____10754 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10769 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10769 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____10805  -> dummy :: env2) env1)
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
                                          let uu____10849 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10849)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_10857 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_10857.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_10857.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10858 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10864  ->
                                 let uu____10865 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10865);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_10880 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_10880.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_10880.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_10880.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_10880.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_10880.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_10880.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_10880.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_10880.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Debug uu____10884)::uu____10885 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10896 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10896 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____10932  -> dummy :: env2) env1)
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
                                          let uu____10976 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10976)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_10984 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_10984.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_10984.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10985 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10991  ->
                                 let uu____10992 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10992);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11007 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11007.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11007.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11007.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11007.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11007.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11007.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11007.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11007.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11011)::uu____11012 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11025 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11025 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11061  -> dummy :: env2) env1)
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
                                          let uu____11105 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11105)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11113 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11113.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11113.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11114 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11120  ->
                                 let uu____11121 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11121);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11136 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11136.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11136.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11136.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11136.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11136.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11136.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11136.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11136.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11140)::uu____11141 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11156 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11156 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11192  -> dummy :: env2) env1)
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
                                          let uu____11236 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11236)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11244 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11244.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11244.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11245 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11251  ->
                                 let uu____11252 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11252);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11267 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11267.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11267.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11267.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11267.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11267.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11267.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11267.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11267.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11271)::uu____11272 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11287 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11287 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11323  -> dummy :: env2) env1)
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
                                          let uu____11367 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11367)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11375 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11375.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11375.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11376 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11382  ->
                                 let uu____11383 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11383);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11398 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11398.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11398.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11398.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11398.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11398.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11398.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11398.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11398.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (CBVApp uu____11402)::uu____11403 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11418 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11418 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11454  -> dummy :: env2) env1)
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
                                          let uu____11498 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11498)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11506 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11506.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11506.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11507 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11513  ->
                                 let uu____11514 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11514);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11529 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11529.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11529.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11529.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11529.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11529.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11529.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11529.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11529.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____11533)::uu____11534 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11553 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11553 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11589  -> dummy :: env2) env1)
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
                                          let uu____11633 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11633)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11641 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11641.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11641.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11642 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11648  ->
                                 let uu____11649 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11649);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11664 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11664.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11664.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11664.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11664.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11664.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11664.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11664.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11664.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____11672 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11672 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11708  -> dummy :: env2) env1)
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
                                          let uu____11752 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11752)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1442_11760 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1442_11760.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1442_11760.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11761 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11767  ->
                                 let uu____11768 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11768);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1449_11783 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1449_11783.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1449_11783.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1449_11783.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1449_11783.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1449_11783.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1449_11783.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1449_11783.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1449_11783.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head,args) ->
               let strict_args =
                 let uu____11819 =
                   let uu____11820 = FStar_Syntax_Util.un_uinst head  in
                   uu____11820.FStar_Syntax_Syntax.n  in
                 match uu____11819 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11829 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____11850  ->
                              fun stack2  ->
                                match uu____11850 with
                                | (a,aq) ->
                                    let uu____11862 =
                                      let uu____11863 =
                                        let uu____11870 =
                                          let uu____11871 =
                                            let uu____11903 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env1, a, uu____11903, false)  in
                                          Clos uu____11871  in
                                        (uu____11870, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11863  in
                                    uu____11862 :: stack2) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11971  ->
                          let uu____11972 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11972);
                     norm cfg env1 stack2 head)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____12023  ->
                              match uu____12023 with
                              | (a,i) ->
                                  let uu____12034 = norm cfg env1 [] a  in
                                  (uu____12034, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____12040 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____12055 = FStar_List.nth norm_args i
                                    in
                                 match uu____12055 with
                                 | (arg_i,uu____12066) ->
                                     let uu____12067 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____12067 with
                                      | (head1,uu____12086) ->
                                          let uu____12111 =
                                            let uu____12112 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____12112.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____12111 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____12116 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____12119 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____12119
                                           | uu____12120 -> false)))))
                       in
                    if uu____12040
                    then
                      let stack2 =
                        FStar_All.pipe_right stack1
                          (FStar_List.fold_right
                             (fun uu____12137  ->
                                fun stack2  ->
                                  match uu____12137 with
                                  | (a,aq) ->
                                      let uu____12149 =
                                        let uu____12150 =
                                          let uu____12157 =
                                            let uu____12158 =
                                              let uu____12190 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env1, a, uu____12190, false)
                                               in
                                            Clos uu____12158  in
                                          (uu____12157, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____12150  in
                                      uu____12149 :: stack2) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12272  ->
                            let uu____12273 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12273);
                       norm cfg env1 stack2 head)
                    else
                      (let head1 = closure_as_term cfg env1 head  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head1 norm_args
                           FStar_Pervasives_Native.None
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env1 stack1 term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12293) when
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
                             ((let uu___1511_12338 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1511_12338.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1511_12338.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env1 stack1 t2
                  | uu____12339 ->
                      let uu____12354 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 uu____12354)
               else
                 (let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12358 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12358 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env1) [] f1  in
                      let t2 =
                        let uu____12389 =
                          let uu____12390 =
                            let uu____12397 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1520_12403 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1520_12403.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1520_12403.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12397)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12390  in
                        mk uu____12389 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12427 = closure_as_term cfg env1 t1  in
                 rebuild cfg env1 stack1 uu____12427
               else
                 (let uu____12430 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12430 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12438 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env2  ->
                                  fun uu____12464  -> dummy :: env2) env1)
                           in
                        norm_comp cfg uu____12438 c1  in
                      let t2 =
                        let uu____12488 = norm_binders cfg env1 bs1  in
                        FStar_Syntax_Util.arrow uu____12488 c2  in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env1 stack1 t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12601)::uu____12602 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12615  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (Arg uu____12617)::uu____12618 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12629  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (App
                    (uu____12631,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12632;
                                   FStar_Syntax_Syntax.vars = uu____12633;_},uu____12634,uu____12635))::uu____12636
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12643  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (MemoLazy uu____12645)::uu____12646 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12657  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | uu____12659 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12662  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env1 [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12667  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12693 = norm cfg env1 [] t2  in
                             FStar_Util.Inl uu____12693
                         | FStar_Util.Inr c ->
                             let uu____12707 = norm_comp cfg env1 c  in
                             FStar_Util.Inr uu____12707
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env1 [])  in
                       match stack1 with
                       | (Cfg cfg1)::stack2 ->
                           let t2 =
                             let uu____12730 =
                               let uu____12731 =
                                 let uu____12758 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12758, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12731
                                in
                             mk uu____12730 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env1 stack2 t2
                       | uu____12793 ->
                           let uu____12794 =
                             let uu____12795 =
                               let uu____12796 =
                                 let uu____12823 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12823, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12796
                                in
                             mk uu____12795 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env1 stack1 uu____12794))))
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
                   let uu___1599_12901 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1601_12904 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1601_12904.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1599_12901.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1599_12901.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1599_12901.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1599_12901.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1599_12901.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1599_12901.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1599_12901.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1599_12901.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____12945 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12945 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1614_12965 = cfg  in
                               let uu____12966 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1614_12965.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12966;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1614_12965.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1614_12965.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1614_12965.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1614_12965.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1614_12965.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1614_12965.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1614_12965.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____12973 =
                                 let uu____12974 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env1 [] uu____12974  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12973
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1621_12977 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1621_12977.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1621_12977.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1621_12977.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1621_12977.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12978 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env1 stack1 uu____12978
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12991,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12992;
                               FStar_Syntax_Syntax.lbunivs = uu____12993;
                               FStar_Syntax_Syntax.lbtyp = uu____12994;
                               FStar_Syntax_Syntax.lbeff = uu____12995;
                               FStar_Syntax_Syntax.lbdef = uu____12996;
                               FStar_Syntax_Syntax.lbattrs = uu____12997;
                               FStar_Syntax_Syntax.lbpos = uu____12998;_}::uu____12999),uu____13000)
               -> rebuild cfg env1 stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let uu____13045 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
               if uu____13045
               then
                 let binder =
                   let uu____13049 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13049  in
                 let def =
                   FStar_Syntax_Util.unmeta_lift lb.FStar_Syntax_Syntax.lbdef
                    in
                 let env2 =
                   let uu____13060 =
                     let uu____13067 =
                       let uu____13068 =
                         let uu____13100 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env1, def, uu____13100, false)  in
                       Clos uu____13068  in
                     ((FStar_Pervasives_Native.Some binder), uu____13067)  in
                   uu____13060 :: env1  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____13175  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env2 stack1 body)
               else
                 (let uu____13179 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu____13182 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff
                          in
                       FStar_Syntax_Util.is_div_effect uu____13182)
                     in
                  if uu____13179
                  then
                    let ffun =
                      let uu____13187 =
                        let uu____13194 =
                          let uu____13195 =
                            let uu____13214 =
                              let uu____13223 =
                                let uu____13230 =
                                  FStar_All.pipe_right
                                    lb.FStar_Syntax_Syntax.lbname
                                    FStar_Util.left
                                   in
                                FStar_Syntax_Syntax.mk_binder uu____13230  in
                              [uu____13223]  in
                            (uu____13214, body, FStar_Pervasives_Native.None)
                             in
                          FStar_Syntax_Syntax.Tm_abs uu____13195  in
                        FStar_Syntax_Syntax.mk uu____13194  in
                      uu____13187 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    let stack2 =
                      (CBVApp
                         (env1, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack1  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____13264  ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env1 stack2 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____13271  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____13273 = closure_as_term cfg env1 t1  in
                        rebuild cfg env1 stack1 uu____13273))
                    else
                      (let uu____13276 =
                         let uu____13281 =
                           let uu____13282 =
                             let uu____13289 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____13289
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____13282]  in
                         FStar_Syntax_Subst.open_term uu____13281 body  in
                       match uu____13276 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____13316  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____13325 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____13325  in
                               FStar_Util.Inl
                                 (let uu___1668_13341 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1668_13341.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1668_13341.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____13344  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1673_13347 = lb  in
                                let uu____13348 =
                                  norm cfg env1 []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____13351 =
                                  FStar_List.map (norm cfg env1 [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1673_13347.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1673_13347.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____13348;
                                  FStar_Syntax_Syntax.lbattrs = uu____13351;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1673_13347.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____13386  -> dummy :: env2)
                                     env1)
                                 in
                              let stack2 = (Cfg cfg) :: stack1  in
                              let cfg1 =
                                let uu___1680_13411 = cfg  in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1680_13411.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1680_13411.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1680_13411.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1680_13411.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1680_13411.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1680_13411.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1680_13411.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1680_13411.FStar_TypeChecker_Cfg.reifying)
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____13415  ->
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
               let uu____13436 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13436 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp
                              in
                           let lbname =
                             let uu____13472 =
                               let uu___1696_13473 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1696_13473.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1696_13473.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13472  in
                           let uu____13474 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13474 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env1 xs  in
                               let env2 =
                                 let uu____13500 =
                                   FStar_List.map (fun uu____13522  -> dummy)
                                     xs1
                                    in
                                 let uu____13529 =
                                   let uu____13538 =
                                     FStar_List.map
                                       (fun uu____13554  -> dummy) lbs1
                                      in
                                   FStar_List.append uu____13538 env1  in
                                 FStar_List.append uu____13500 uu____13529
                                  in
                               let def_body1 = norm cfg env2 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13574 =
                                       let uu___1710_13575 = rc  in
                                       let uu____13576 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env2 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1710_13575.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13576;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1710_13575.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13574
                                 | uu____13585 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1715_13591 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1715_13591.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1715_13591.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1715_13591.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1715_13591.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13601 =
                        FStar_List.map (fun uu____13617  -> dummy) lbs2  in
                      FStar_List.append uu____13601 env1  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13625 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13625 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1724_13641 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1724_13641.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1724_13641.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env1 stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu____13675 = closure_as_term cfg env1 t1  in
               rebuild cfg env1 stack1 uu____13675
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13696 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13774  ->
                        match uu____13774 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1740_13899 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1740_13899.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1740_13899.FStar_Syntax_Syntax.sort)
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
               (match uu____13696 with
                | (rec_env,memos,uu____14090) ->
                    let uu____14145 =
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
                             let uu____14394 =
                               let uu____14401 =
                                 let uu____14402 =
                                   let uu____14434 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14434, false)
                                    in
                                 Clos uu____14402  in
                               (FStar_Pervasives_Native.None, uu____14401)
                                in
                             uu____14394 :: env2)
                        (FStar_Pervasives_Native.snd lbs) env1
                       in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14519  ->
                     let uu____14520 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14520);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14544 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env1 stack1 head
                     else
                       (match stack1 with
                        | uu____14548::uu____14549 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14554) ->
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
                             | uu____14633 -> norm cfg env1 stack1 head)
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
                                  let uu____14681 =
                                    let uu____14702 =
                                      norm_pattern_args cfg env1 args  in
                                    (names1, uu____14702)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14681
                              | uu____14731 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head1, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env1 stack1 t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14737 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env1 stack1 t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14753 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14767 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14781 =
                        let uu____14783 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14785 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14783 uu____14785
                         in
                      failwith uu____14781
                    else
                      (let uu____14790 = inline_closure_env cfg env1 [] t2
                          in
                       rebuild cfg env1 stack1 uu____14790)
                | uu____14791 -> norm cfg env1 stack1 t2))

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
              let uu____14800 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14800 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14814  ->
                        let uu____14815 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14815);
                   rebuild cfg env1 stack1 t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14828  ->
                        let uu____14829 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14831 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14829 uu____14831);
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
                      | (UnivArgs (us',uu____14844))::stack2 ->
                          ((let uu____14853 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14853
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14861 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14861) us'
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
                      | uu____14897 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env1 stack1 t1
                      | uu____14900 ->
                          let uu____14903 =
                            let uu____14905 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14905
                             in
                          failwith uu____14903
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
              let uu____14925 =
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
                    let uu___1851_14943 = cfg  in
                    let uu____14944 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps
                       in
                    {
                      FStar_TypeChecker_Cfg.steps = uu____14944;
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1851_14943.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1851_14943.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        [FStar_TypeChecker_Env.InliningDelta;
                        FStar_TypeChecker_Env.Eager_unfolding_only];
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1851_14943.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1851_14943.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1851_14943.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1851_14943.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1851_14943.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  (cfg', ((Cfg cfg) :: stack1))
                else (cfg, stack1)  in
              match uu____14925 with
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
                     (uu____14985,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14986;
                                    FStar_Syntax_Syntax.vars = uu____14987;_},uu____14988,uu____14989))::uu____14990
                     -> ()
                 | uu____14995 ->
                     let uu____14998 =
                       let uu____15000 = stack_to_string stack1  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____15000
                        in
                     failwith uu____14998);
                (let top0 = top  in
                 let top1 = FStar_Syntax_Util.unascribe top  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____15009  ->
                      let uu____15010 = FStar_Syntax_Print.tag_of_term top1
                         in
                      let uu____15012 =
                        FStar_Syntax_Print.term_to_string top1  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____15010
                        uu____15012);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1  in
                  let uu____15016 =
                    let uu____15017 = FStar_Syntax_Subst.compress top2  in
                    uu____15017.FStar_Syntax_Syntax.n  in
                  match uu____15016 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m
                         in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name
                         in
                      let uu____15039 =
                        let uu____15048 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr
                           in
                        FStar_All.pipe_right uu____15048 FStar_Util.must  in
                      (match uu____15039 with
                       | (uu____15063,repr) ->
                           let uu____15073 =
                             let uu____15080 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr
                                in
                             FStar_All.pipe_right uu____15080 FStar_Util.must
                              in
                           (match uu____15073 with
                            | (uu____15117,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15123 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15134 =
                                         let uu____15135 =
                                           FStar_Syntax_Subst.compress e  in
                                         uu____15135.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15134 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15141,uu____15142))
                                           ->
                                           let uu____15151 =
                                             let uu____15152 =
                                               FStar_Syntax_Subst.compress e1
                                                in
                                             uu____15152.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____15151 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15158,msrc,uu____15160))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15169 =
                                                  FStar_Syntax_Subst.compress
                                                    e2
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____15169
                                            | uu____15170 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15171 ->
                                           FStar_Pervasives_Native.None
                                        in
                                     let uu____15172 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     (match uu____15172 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___1930_15177 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___1930_15177.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___1930_15177.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___1930_15177.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e;
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___1930_15177.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___1930_15177.FStar_Syntax_Syntax.lbpos)
                                            }  in
                                          let uu____15178 =
                                            FStar_List.tl stack1  in
                                          let uu____15179 =
                                            let uu____15180 =
                                              let uu____15187 =
                                                let uu____15188 =
                                                  let uu____15202 =
                                                    FStar_Syntax_Util.mk_reify
                                                      body
                                                     in
                                                  ((false, [lb1]),
                                                    uu____15202)
                                                   in
                                                FStar_Syntax_Syntax.Tm_let
                                                  uu____15188
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____15187
                                               in
                                            uu____15180
                                              FStar_Pervasives_Native.None
                                              top2.FStar_Syntax_Syntax.pos
                                             in
                                          norm cfg env1 uu____15178
                                            uu____15179
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15218 =
                                            let uu____15220 = is_return body
                                               in
                                            match uu____15220 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15225;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15226;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15229 -> false  in
                                          if uu____15218
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
                                             let uu____15244 =
                                               let bv =
                                                 FStar_Syntax_Syntax.new_bv
                                                   FStar_Pervasives_Native.None
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let lb1 =
                                                 let uu____15253 =
                                                   let uu____15256 =
                                                     let uu____15267 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         x.FStar_Syntax_Syntax.sort
                                                        in
                                                     [uu____15267]  in
                                                   FStar_Syntax_Util.mk_app
                                                     repr uu____15256
                                                    in
                                                 let uu____15292 =
                                                   let uu____15293 =
                                                     FStar_TypeChecker_Env.is_total_effect
                                                       cfg.FStar_TypeChecker_Cfg.tcenv
                                                       eff_name
                                                      in
                                                   if uu____15293
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
                                                     = uu____15253;
                                                   FStar_Syntax_Syntax.lbeff
                                                     = uu____15292;
                                                   FStar_Syntax_Syntax.lbdef
                                                     = head;
                                                   FStar_Syntax_Syntax.lbattrs
                                                     = [];
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (head.FStar_Syntax_Syntax.pos)
                                                 }  in
                                               let uu____15300 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   bv
                                                  in
                                               (lb1, bv, uu____15300)  in
                                             match uu____15244 with
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
                                                   let uu____15317 =
                                                     let uu____15324 =
                                                       let uu____15325 =
                                                         let uu____15344 =
                                                           let uu____15353 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x
                                                              in
                                                           [uu____15353]  in
                                                         (uu____15344, body1,
                                                           (FStar_Pervasives_Native.Some
                                                              body_rc))
                                                          in
                                                       FStar_Syntax_Syntax.Tm_abs
                                                         uu____15325
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____15324
                                                      in
                                                   uu____15317
                                                     FStar_Pervasives_Native.None
                                                     body1.FStar_Syntax_Syntax.pos
                                                    in
                                                 let close =
                                                   closure_as_term cfg env1
                                                    in
                                                 let bind_inst =
                                                   let uu____15392 =
                                                     let uu____15393 =
                                                       FStar_Syntax_Subst.compress
                                                         bind_repr
                                                        in
                                                     uu____15393.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____15392 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (bind,uu____15399::uu____15400::[])
                                                       ->
                                                       let uu____15405 =
                                                         let uu____15412 =
                                                           let uu____15413 =
                                                             let uu____15420
                                                               =
                                                               let uu____15421
                                                                 =
                                                                 let uu____15422
                                                                   =
                                                                   close
                                                                    lb.FStar_Syntax_Syntax.lbtyp
                                                                    in
                                                                 (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                                   uu____15422
                                                                  in
                                                               let uu____15423
                                                                 =
                                                                 let uu____15426
                                                                   =
                                                                   let uu____15427
                                                                    = 
                                                                    close t
                                                                     in
                                                                   (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                    cfg.FStar_TypeChecker_Cfg.tcenv
                                                                    uu____15427
                                                                    in
                                                                 [uu____15426]
                                                                  in
                                                               uu____15421 ::
                                                                 uu____15423
                                                                in
                                                             (bind,
                                                               uu____15420)
                                                              in
                                                           FStar_Syntax_Syntax.Tm_uinst
                                                             uu____15413
                                                            in
                                                         FStar_Syntax_Syntax.mk
                                                           uu____15412
                                                          in
                                                       uu____15405
                                                         FStar_Pervasives_Native.None
                                                         rng
                                                   | uu____15430 ->
                                                       failwith
                                                         "NIY : Reification of indexed effects"
                                                    in
                                                 let maybe_range_arg =
                                                   let uu____15445 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____15445
                                                   then
                                                     let uu____15458 =
                                                       let uu____15467 =
                                                         FStar_TypeChecker_Cfg.embed_simple
                                                           FStar_Syntax_Embeddings.e_range
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                          in
                                                       FStar_Syntax_Syntax.as_arg
                                                         uu____15467
                                                        in
                                                     let uu____15468 =
                                                       let uu____15479 =
                                                         let uu____15488 =
                                                           FStar_TypeChecker_Cfg.embed_simple
                                                             FStar_Syntax_Embeddings.e_range
                                                             body2.FStar_Syntax_Syntax.pos
                                                             body2.FStar_Syntax_Syntax.pos
                                                            in
                                                         FStar_Syntax_Syntax.as_arg
                                                           uu____15488
                                                          in
                                                       [uu____15479]  in
                                                     uu____15458 ::
                                                       uu____15468
                                                   else []  in
                                                 let reified =
                                                   let args =
                                                     let uu____15537 =
                                                       FStar_Syntax_Util.is_layered
                                                         ed
                                                        in
                                                     if uu____15537
                                                     then
                                                       let unit_args =
                                                         let uu____15561 =
                                                           let uu____15562 =
                                                             let uu____15565
                                                               =
                                                               let uu____15566
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15566
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15565
                                                               FStar_Syntax_Subst.compress
                                                              in
                                                           uu____15562.FStar_Syntax_Syntax.n
                                                            in
                                                         match uu____15561
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_arrow
                                                             (uu____15607::uu____15608::bs,uu____15610)
                                                             when
                                                             (FStar_List.length
                                                                bs)
                                                               >=
                                                               (Prims.of_int (2))
                                                             ->
                                                             let uu____15662
                                                               =
                                                               let uu____15671
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   bs
                                                                   (FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2))))
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15671
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15662
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____15802
                                                                     ->
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.unit_const))
                                                         | uu____15809 ->
                                                             let uu____15810
                                                               =
                                                               let uu____15816
                                                                 =
                                                                 let uu____15818
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    ed.FStar_Syntax_Syntax.mname
                                                                    in
                                                                 let uu____15820
                                                                   =
                                                                   let uu____15822
                                                                    =
                                                                    let uu____15823
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    ed
                                                                    FStar_Syntax_Util.get_bind_vc_combinator
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15823
                                                                    FStar_Pervasives_Native.snd
                                                                     in
                                                                   FStar_All.pipe_right
                                                                    uu____15822
                                                                    FStar_Syntax_Print.term_to_string
                                                                    in
                                                                 FStar_Util.format2
                                                                   "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                                   uu____15818
                                                                   uu____15820
                                                                  in
                                                               (FStar_Errors.Fatal_UnexpectedEffect,
                                                                 uu____15816)
                                                                in
                                                             FStar_Errors.raise_error
                                                               uu____15810
                                                               rng
                                                          in
                                                       let uu____15857 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let uu____15866 =
                                                         let uu____15877 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t
                                                            in
                                                         let uu____15886 =
                                                           let uu____15897 =
                                                             let uu____15908
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head1
                                                                in
                                                             let uu____15917
                                                               =
                                                               let uu____15928
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   body2
                                                                  in
                                                               [uu____15928]
                                                                in
                                                             uu____15908 ::
                                                               uu____15917
                                                              in
                                                           FStar_List.append
                                                             unit_args
                                                             uu____15897
                                                            in
                                                         uu____15877 ::
                                                           uu____15886
                                                          in
                                                       uu____15857 ::
                                                         uu____15866
                                                     else
                                                       (let uu____15987 =
                                                          let uu____15998 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              lb.FStar_Syntax_Syntax.lbtyp
                                                             in
                                                          let uu____16007 =
                                                            let uu____16018 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t
                                                               in
                                                            [uu____16018]  in
                                                          uu____15998 ::
                                                            uu____16007
                                                           in
                                                        let uu____16051 =
                                                          let uu____16062 =
                                                            let uu____16073 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            let uu____16082 =
                                                              let uu____16093
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  head1
                                                                 in
                                                              let uu____16102
                                                                =
                                                                let uu____16113
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.tun
                                                                   in
                                                                let uu____16122
                                                                  =
                                                                  let uu____16133
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    body2  in
                                                                  [uu____16133]
                                                                   in
                                                                uu____16113
                                                                  ::
                                                                  uu____16122
                                                                 in
                                                              uu____16093 ::
                                                                uu____16102
                                                               in
                                                            uu____16073 ::
                                                              uu____16082
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____16062
                                                           in
                                                        FStar_List.append
                                                          uu____15987
                                                          uu____16051)
                                                      in
                                                   let uu____16198 =
                                                     let uu____16205 =
                                                       let uu____16206 =
                                                         let uu____16220 =
                                                           let uu____16223 =
                                                             let uu____16230
                                                               =
                                                               let uu____16231
                                                                 =
                                                                 FStar_Syntax_Syntax.mk_binder
                                                                   head_bv
                                                                  in
                                                               [uu____16231]
                                                                in
                                                             FStar_Syntax_Subst.close
                                                               uu____16230
                                                              in
                                                           let uu____16250 =
                                                             FStar_Syntax_Syntax.mk
                                                               (FStar_Syntax_Syntax.Tm_app
                                                                  (bind_inst,
                                                                    args))
                                                               FStar_Pervasives_Native.None
                                                               rng
                                                              in
                                                           FStar_All.pipe_left
                                                             uu____16223
                                                             uu____16250
                                                            in
                                                         ((false, [lb_head]),
                                                           uu____16220)
                                                          in
                                                       FStar_Syntax_Syntax.Tm_let
                                                         uu____16206
                                                        in
                                                     FStar_Syntax_Syntax.mk
                                                       uu____16205
                                                      in
                                                   uu____16198
                                                     FStar_Pervasives_Native.None
                                                     rng
                                                    in
                                                 (FStar_TypeChecker_Cfg.log
                                                    cfg
                                                    (fun uu____16282  ->
                                                       let uu____16283 =
                                                         FStar_Syntax_Print.term_to_string
                                                           top0
                                                          in
                                                       let uu____16285 =
                                                         FStar_Syntax_Print.term_to_string
                                                           reified
                                                          in
                                                       FStar_Util.print2
                                                         "Reified (1) <%s> to %s\n"
                                                         uu____16283
                                                         uu____16285);
                                                  (let uu____16288 =
                                                     FStar_List.tl stack1  in
                                                   norm cfg env1 uu____16288
                                                     reified)))))))
                  | FStar_Syntax_Syntax.Tm_app (head,args) ->
                      ((let uu____16316 = FStar_Options.defensive ()  in
                        if uu____16316
                        then
                          let is_arg_impure uu____16331 =
                            match uu____16331 with
                            | (e,q) ->
                                let uu____16345 =
                                  let uu____16346 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16346.FStar_Syntax_Syntax.n  in
                                (match uu____16345 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____16362 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____16362
                                 | uu____16364 -> false)
                             in
                          let uu____16366 =
                            let uu____16368 =
                              let uu____16379 =
                                FStar_Syntax_Syntax.as_arg head  in
                              uu____16379 :: args  in
                            FStar_Util.for_some is_arg_impure uu____16368  in
                          (if uu____16366
                           then
                             let uu____16405 =
                               let uu____16411 =
                                 let uu____16413 =
                                   FStar_Syntax_Print.term_to_string top2  in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____16413
                                  in
                               (FStar_Errors.Warning_Defensive, uu____16411)
                                in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu____16405
                           else ())
                        else ());
                       (let fallback1 uu____16426 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16430  ->
                               let uu____16431 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____16431 "");
                          (let uu____16435 = FStar_List.tl stack1  in
                           let uu____16436 = FStar_Syntax_Util.mk_reify top2
                              in
                           norm cfg env1 uu____16435 uu____16436)
                           in
                        let fallback2 uu____16442 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16446  ->
                               let uu____16447 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____16447 "");
                          (let uu____16451 = FStar_List.tl stack1  in
                           let uu____16452 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env1 uu____16451 uu____16452)
                           in
                        let uu____16457 =
                          let uu____16458 = FStar_Syntax_Util.un_uinst head
                             in
                          uu____16458.FStar_Syntax_Syntax.n  in
                        match uu____16457 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____16464 =
                              let uu____16466 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____16466  in
                            if uu____16464
                            then fallback1 ()
                            else
                              (let uu____16471 =
                                 let uu____16473 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____16473  in
                               if uu____16471
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____16490 =
                                      let uu____16495 =
                                        FStar_Syntax_Util.mk_reify head  in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____16495 args
                                       in
                                    uu____16490 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____16496 = FStar_List.tl stack1  in
                                  norm cfg env1 uu____16496 t1))
                        | uu____16497 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____16499) ->
                      do_reify_monadic fallback cfg env1 stack1 e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____16523 = closure_as_term cfg env1 t'  in
                        reify_lift cfg e msrc mtgt uu____16523  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____16527  ->
                            let uu____16528 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____16528);
                       (let uu____16531 = FStar_List.tl stack1  in
                        norm cfg env1 uu____16531 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches1) ->
                      let branches2 =
                        FStar_All.pipe_right branches1
                          (FStar_List.map
                             (fun uu____16652  ->
                                match uu____16652 with
                                | (pat,wopt,tm) ->
                                    let uu____16700 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16700)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches2))
                          top2.FStar_Syntax_Syntax.pos
                         in
                      let uu____16732 = FStar_List.tl stack1  in
                      norm cfg env1 uu____16732 tm
                  | uu____16733 -> fallback ()))

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
              (fun uu____16747  ->
                 let uu____16748 = FStar_Ident.string_of_lid msrc  in
                 let uu____16750 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16752 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16748
                   uu____16750 uu____16752);
            (let uu____16755 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16758 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env1)
                     in
                  Prims.op_Negation uu____16758)
                in
             if uu____16755
             then
               let ed =
                 let uu____16763 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env1 uu____16763  in
               let uu____16764 =
                 let uu____16773 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 FStar_All.pipe_right uu____16773 FStar_Util.must  in
               match uu____16764 with
               | (uu____16820,repr) ->
                   let uu____16830 =
                     let uu____16839 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr
                        in
                     FStar_All.pipe_right uu____16839 FStar_Util.must  in
                   (match uu____16830 with
                    | (uu____16886,return_repr) ->
                        let return_inst =
                          let uu____16899 =
                            let uu____16900 =
                              FStar_Syntax_Subst.compress return_repr  in
                            uu____16900.FStar_Syntax_Syntax.n  in
                          match uu____16899 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm,uu____16906::[]) ->
                              let uu____16911 =
                                let uu____16918 =
                                  let uu____16919 =
                                    let uu____16926 =
                                      let uu____16927 =
                                        env1.FStar_TypeChecker_Env.universe_of
                                          env1 t
                                         in
                                      [uu____16927]  in
                                    (return_tm, uu____16926)  in
                                  FStar_Syntax_Syntax.Tm_uinst uu____16919
                                   in
                                FStar_Syntax_Syntax.mk uu____16918  in
                              uu____16911 FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                          | uu____16930 ->
                              failwith "NIY : Reification of indexed effects"
                           in
                        let uu____16934 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t
                             in
                          let lb =
                            let uu____16945 =
                              let uu____16948 =
                                let uu____16959 =
                                  FStar_Syntax_Syntax.as_arg t  in
                                [uu____16959]  in
                              FStar_Syntax_Util.mk_app repr uu____16948  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Util.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu____16945;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            }  in
                          let uu____16986 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (lb, bv, uu____16986)  in
                        (match uu____16934 with
                         | (lb_e,e_bv,e1) ->
                             let uu____16998 =
                               let uu____17005 =
                                 let uu____17006 =
                                   let uu____17020 =
                                     let uu____17023 =
                                       let uu____17030 =
                                         let uu____17031 =
                                           FStar_Syntax_Syntax.mk_binder e_bv
                                            in
                                         [uu____17031]  in
                                       FStar_Syntax_Subst.close uu____17030
                                        in
                                     let uu____17050 =
                                       let uu____17051 =
                                         let uu____17058 =
                                           let uu____17059 =
                                             let uu____17076 =
                                               let uu____17087 =
                                                 FStar_Syntax_Syntax.as_arg t
                                                  in
                                               let uu____17096 =
                                                 let uu____17107 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     e1
                                                    in
                                                 [uu____17107]  in
                                               uu____17087 :: uu____17096  in
                                             (return_inst, uu____17076)  in
                                           FStar_Syntax_Syntax.Tm_app
                                             uu____17059
                                            in
                                         FStar_Syntax_Syntax.mk uu____17058
                                          in
                                       uu____17051
                                         FStar_Pervasives_Native.None
                                         e1.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_All.pipe_left uu____17023
                                       uu____17050
                                      in
                                   ((false, [lb_e]), uu____17020)  in
                                 FStar_Syntax_Syntax.Tm_let uu____17006  in
                               FStar_Syntax_Syntax.mk uu____17005  in
                             uu____16998 FStar_Pervasives_Native.None
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu____17169 =
                  FStar_TypeChecker_Env.monad_leq env1 msrc mtgt  in
                match uu____17169 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17172 =
                      let uu____17174 = FStar_Ident.string_of_lid msrc  in
                      let uu____17176 = FStar_Ident.string_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17174 uu____17176
                       in
                    failwith uu____17172
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17179;
                      FStar_TypeChecker_Env.mtarget = uu____17180;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17181;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17201 =
                      let uu____17203 = FStar_Ident.string_of_lid msrc  in
                      let uu____17205 = FStar_Ident.string_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17203 uu____17205
                       in
                    failwith uu____17201
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17208;
                      FStar_TypeChecker_Env.mtarget = uu____17209;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17210;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____17241 =
                        FStar_TypeChecker_Env.is_reifiable_effect env1 msrc
                         in
                      if uu____17241
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____17246 =
                           let uu____17253 =
                             let uu____17254 =
                               let uu____17273 =
                                 let uu____17282 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____17282]  in
                               (uu____17273, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____17254  in
                           FStar_Syntax_Syntax.mk uu____17253  in
                         uu____17246 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____17315 =
                      env1.FStar_TypeChecker_Env.universe_of env1 t  in
                    lift uu____17315 t e1))

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
                (fun uu____17385  ->
                   match uu____17385 with
                   | (a,imp) ->
                       let uu____17404 = norm cfg env1 [] a  in
                       (uu____17404, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env1  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17414  ->
             let uu____17415 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17417 =
               FStar_Util.string_of_int (FStar_List.length env1)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17415 uu____17417);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env1 [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17443 = norm_universe cfg env1 u  in
                   FStar_All.pipe_left
                     (fun uu____17446  ->
                        FStar_Pervasives_Native.Some uu____17446) uu____17443
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2111_17447 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2111_17447.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2111_17447.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env1 [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17469 = norm_universe cfg env1 u  in
                   FStar_All.pipe_left
                     (fun uu____17472  ->
                        FStar_Pervasives_Native.Some uu____17472) uu____17469
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2122_17473 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2122_17473.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2122_17473.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17518  ->
                      match uu____17518 with
                      | (a,i) ->
                          let uu____17538 = norm cfg env1 [] a  in
                          (uu____17538, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17560  ->
                       match uu___14_17560 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17564 = norm cfg env1 [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17564
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env1)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env1 [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2139_17572 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2141_17575 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2141_17575.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2139_17572.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2139_17572.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env1  ->
      fun b  ->
        let uu____17579 = b  in
        match uu____17579 with
        | (x,imp) ->
            let x1 =
              let uu___2149_17587 = x  in
              let uu____17588 = norm cfg env1 [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2149_17587.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2149_17587.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17588
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____17599 =
                    let uu____17600 = closure_as_term cfg env1 t  in
                    FStar_Syntax_Syntax.Meta uu____17600  in
                  FStar_Pervasives_Native.Some uu____17599
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env1  ->
      fun bs  ->
        let uu____17611 =
          FStar_List.fold_left
            (fun uu____17645  ->
               fun b  ->
                 match uu____17645 with
                 | (nbs',env2) ->
                     let b1 = norm_binder cfg env2 b  in
                     ((b1 :: nbs'), (dummy :: env2))) ([], env1) bs
           in
        match uu____17611 with | (nbs,uu____17725) -> FStar_List.rev nbs

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
            let uu____17757 =
              let uu___2174_17758 = rc  in
              let uu____17759 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env1 [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2174_17758.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17759;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2174_17758.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17757
        | uu____17777 -> lopt

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
            (let uu____17787 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17789 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17787 uu____17789)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_17801  ->
      match uu___15_17801 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17814 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17814 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17818 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____17818)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun tm  ->
          let tm1 =
            let uu____17826 = norm_cb cfg  in
            reduce_primops uu____17826 cfg env1 tm  in
          let uu____17831 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17831
          then tm1
          else
            (let w t =
               let uu___2203_17850 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2203_17850.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2203_17850.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17862 =
                 let uu____17863 = FStar_Syntax_Util.unmeta t  in
                 uu____17863.FStar_Syntax_Syntax.n  in
               match uu____17862 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17875 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17939)::args1,(bv,uu____17942)::bs1) ->
                   let uu____17996 =
                     let uu____17997 = FStar_Syntax_Subst.compress t  in
                     uu____17997.FStar_Syntax_Syntax.n  in
                   (match uu____17996 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18002 -> false)
               | ([],[]) -> true
               | (uu____18033,uu____18034) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18085 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18087 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18085
                    uu____18087)
               else ();
               (let uu____18092 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18092 with
                | (hd,args) ->
                    let uu____18131 =
                      let uu____18132 = FStar_Syntax_Subst.compress hd  in
                      uu____18132.FStar_Syntax_Syntax.n  in
                    (match uu____18131 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____18140 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18142 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18144 =
                               FStar_Syntax_Print.term_to_string hd  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18140 uu____18142 uu____18144)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18149 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18167 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18169 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18167
                    uu____18169)
               else ();
               (let uu____18174 = FStar_Syntax_Util.is_squash t  in
                match uu____18174 with
                | FStar_Pervasives_Native.Some (uu____18185,t') ->
                    is_applied bs t'
                | uu____18197 ->
                    let uu____18206 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18206 with
                     | FStar_Pervasives_Native.Some (uu____18217,t') ->
                         is_applied bs t'
                     | uu____18229 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18253 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18253 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18260)::(q,uu____18262)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18305 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18307 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18305 uu____18307)
                    else ();
                    (let uu____18312 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18312 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18317 =
                           let uu____18318 = FStar_Syntax_Subst.compress p
                              in
                           uu____18318.FStar_Syntax_Syntax.n  in
                         (match uu____18317 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18329 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18329))
                          | uu____18332 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18335)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18360 =
                           let uu____18361 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18361.FStar_Syntax_Syntax.n  in
                         (match uu____18360 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18372 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18372))
                          | uu____18375 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18379 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18379 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18384 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18384 with
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
                                     let uu____18398 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18398))
                               | uu____18401 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18406)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18431 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18431 with
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
                                     let uu____18445 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18445))
                               | uu____18448 -> FStar_Pervasives_Native.None)
                          | uu____18451 -> FStar_Pervasives_Native.None)
                     | uu____18454 -> FStar_Pervasives_Native.None))
               | uu____18457 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18470 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18470 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18476)::[],uu____18477,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18497 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18499 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18497
                         uu____18499)
                    else ();
                    is_quantified_const bv phi')
               | uu____18504 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18519 =
                 let uu____18520 = FStar_Syntax_Subst.compress phi  in
                 uu____18520.FStar_Syntax_Syntax.n  in
               match uu____18519 with
               | FStar_Syntax_Syntax.Tm_match (uu____18526,br::brs) ->
                   let uu____18593 = br  in
                   (match uu____18593 with
                    | (uu____18611,uu____18612,e) ->
                        let r =
                          let uu____18634 = simp_t e  in
                          match uu____18634 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18646 =
                                FStar_List.for_all
                                  (fun uu____18665  ->
                                     match uu____18665 with
                                     | (uu____18679,uu____18680,e') ->
                                         let uu____18694 = simp_t e'  in
                                         uu____18694 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18646
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18710 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18720 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18720
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18758 =
                 match uu____18758 with
                 | (t1,q) ->
                     let uu____18779 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18779 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18811 -> (t1, q))
                  in
               let uu____18824 = FStar_Syntax_Util.head_and_args t  in
               match uu____18824 with
               | (head,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18904 =
                 let uu____18905 = FStar_Syntax_Util.unmeta ty  in
                 uu____18905.FStar_Syntax_Syntax.n  in
               match uu____18904 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18910) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18915,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18939 -> false  in
             let simplify arg =
               let uu____18972 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18972, arg)  in
             let uu____18987 = is_forall_const tm1  in
             match uu____18987 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____18993 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18995 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18993
                       uu____18995)
                  else ();
                  (let uu____19000 = norm cfg env1 [] tm'  in
                   maybe_simplify_aux cfg env1 stack1 uu____19000))
             | FStar_Pervasives_Native.None  ->
                 let uu____19001 =
                   let uu____19002 = FStar_Syntax_Subst.compress tm1  in
                   uu____19002.FStar_Syntax_Syntax.n  in
                 (match uu____19001 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19006;
                              FStar_Syntax_Syntax.vars = uu____19007;_},uu____19008);
                         FStar_Syntax_Syntax.pos = uu____19009;
                         FStar_Syntax_Syntax.vars = uu____19010;_},args)
                      ->
                      let uu____19040 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19040
                      then
                        let uu____19043 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        (match uu____19043 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19101)::
                             (uu____19102,(arg,uu____19104))::[] ->
                             maybe_auto_squash arg
                         | (uu____19177,(arg,uu____19179))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19180)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19253)::uu____19254::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19324::(FStar_Pervasives_Native.Some (false
                                         ),uu____19325)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19395 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19413 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19413
                         then
                           let uu____19416 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify)
                              in
                           match uu____19416 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19474)::uu____19475::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19545::(FStar_Pervasives_Native.Some (true
                                           ),uu____19546)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19616)::(uu____19617,(arg,uu____19619))::[]
                               -> maybe_auto_squash arg
                           | (uu____19692,(arg,uu____19694))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19695)::[]
                               -> maybe_auto_squash arg
                           | uu____19768 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19786 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19786
                            then
                              let uu____19789 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify)
                                 in
                              match uu____19789 with
                              | uu____19847::(FStar_Pervasives_Native.Some
                                              (true ),uu____19848)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19918)::uu____19919::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19989)::(uu____19990,(arg,uu____19992))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20065,(p,uu____20067))::(uu____20068,
                                                                (q,uu____20070))::[]
                                  ->
                                  let uu____20142 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20142
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20147 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20165 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20165
                               then
                                 let uu____20168 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify)
                                    in
                                 match uu____20168 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20226)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20227)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20301)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20302)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20376)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20377)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20451)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20452)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20526,(arg,uu____20528))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20529)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20602)::(uu____20603,(arg,uu____20605))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20678,(arg,uu____20680))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20681)::[]
                                     ->
                                     let uu____20754 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20754
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20755)::(uu____20756,(arg,uu____20758))::[]
                                     ->
                                     let uu____20831 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20831
                                 | (uu____20832,(p,uu____20834))::(uu____20835,
                                                                   (q,uu____20837))::[]
                                     ->
                                     let uu____20909 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20909
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20914 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20932 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20932
                                  then
                                    let uu____20935 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify)
                                       in
                                    match uu____20935 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20993)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21037)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21081 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21099 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21099
                                     then
                                       match args with
                                       | (t,uu____21103)::[] ->
                                           let uu____21128 =
                                             let uu____21129 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21129.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21128 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21132::[],body,uu____21134)
                                                ->
                                                let uu____21169 = simp_t body
                                                   in
                                                (match uu____21169 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21175 -> tm1)
                                            | uu____21179 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21181))::(t,uu____21183)::[]
                                           ->
                                           let uu____21223 =
                                             let uu____21224 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21224.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21223 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21227::[],body,uu____21229)
                                                ->
                                                let uu____21264 = simp_t body
                                                   in
                                                (match uu____21264 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21272 -> tm1)
                                            | uu____21276 -> tm1)
                                       | uu____21277 -> tm1
                                     else
                                       (let uu____21290 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21290
                                        then
                                          match args with
                                          | (t,uu____21294)::[] ->
                                              let uu____21319 =
                                                let uu____21320 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21320.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21319 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21323::[],body,uu____21325)
                                                   ->
                                                   let uu____21360 =
                                                     simp_t body  in
                                                   (match uu____21360 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21366 -> tm1)
                                               | uu____21370 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21372))::(t,uu____21374)::[]
                                              ->
                                              let uu____21414 =
                                                let uu____21415 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21415.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21414 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21418::[],body,uu____21420)
                                                   ->
                                                   let uu____21455 =
                                                     simp_t body  in
                                                   (match uu____21455 with
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
                                                    | uu____21463 -> tm1)
                                               | uu____21467 -> tm1)
                                          | uu____21468 -> tm1
                                        else
                                          (let uu____21481 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21481
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21484;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21485;_},uu____21486)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21512;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21513;_},uu____21514)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21540 -> tm1
                                           else
                                             (let uu____21553 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____21553
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____21567 =
                                                    let uu____21568 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____21568.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____21567 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21579 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21593 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____21593
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____21632 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____21632
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21638 =
                                                         let uu____21639 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____21639.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____21638 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21642 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____21650 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____21650
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21659
                                                                  =
                                                                  let uu____21660
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____21660.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____21659
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,uu____21666)
                                                                    -> hd
                                                                | uu____21691
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____21695
                                                                =
                                                                let uu____21706
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____21706]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21695)
                                                       | uu____21739 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21744 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____21744 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21764 ->
                                                     let uu____21773 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____21773 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21779;
                         FStar_Syntax_Syntax.vars = uu____21780;_},args)
                      ->
                      let uu____21806 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21806
                      then
                        let uu____21809 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        (match uu____21809 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21867)::
                             (uu____21868,(arg,uu____21870))::[] ->
                             maybe_auto_squash arg
                         | (uu____21943,(arg,uu____21945))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21946)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22019)::uu____22020::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22090::(FStar_Pervasives_Native.Some (false
                                         ),uu____22091)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22161 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22179 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22179
                         then
                           let uu____22182 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify)
                              in
                           match uu____22182 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22240)::uu____22241::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22311::(FStar_Pervasives_Native.Some (true
                                           ),uu____22312)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22382)::(uu____22383,(arg,uu____22385))::[]
                               -> maybe_auto_squash arg
                           | (uu____22458,(arg,uu____22460))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22461)::[]
                               -> maybe_auto_squash arg
                           | uu____22534 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22552 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22552
                            then
                              let uu____22555 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify)
                                 in
                              match uu____22555 with
                              | uu____22613::(FStar_Pervasives_Native.Some
                                              (true ),uu____22614)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22684)::uu____22685::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22755)::(uu____22756,(arg,uu____22758))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22831,(p,uu____22833))::(uu____22834,
                                                                (q,uu____22836))::[]
                                  ->
                                  let uu____22908 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22908
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22913 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22931 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22931
                               then
                                 let uu____22934 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify)
                                    in
                                 match uu____22934 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22992)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22993)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23067)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23068)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23142)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23143)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23217)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23218)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23292,(arg,uu____23294))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23295)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23368)::(uu____23369,(arg,uu____23371))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23444,(arg,uu____23446))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23447)::[]
                                     ->
                                     let uu____23520 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23520
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23521)::(uu____23522,(arg,uu____23524))::[]
                                     ->
                                     let uu____23597 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23597
                                 | (uu____23598,(p,uu____23600))::(uu____23601,
                                                                   (q,uu____23603))::[]
                                     ->
                                     let uu____23675 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23675
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23680 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23698 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23698
                                  then
                                    let uu____23701 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify)
                                       in
                                    match uu____23701 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23759)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23803)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23847 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23865 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23865
                                     then
                                       match args with
                                       | (t,uu____23869)::[] ->
                                           let uu____23894 =
                                             let uu____23895 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23895.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23894 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23898::[],body,uu____23900)
                                                ->
                                                let uu____23935 = simp_t body
                                                   in
                                                (match uu____23935 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23941 -> tm1)
                                            | uu____23945 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23947))::(t,uu____23949)::[]
                                           ->
                                           let uu____23989 =
                                             let uu____23990 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23990.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23989 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23993::[],body,uu____23995)
                                                ->
                                                let uu____24030 = simp_t body
                                                   in
                                                (match uu____24030 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24038 -> tm1)
                                            | uu____24042 -> tm1)
                                       | uu____24043 -> tm1
                                     else
                                       (let uu____24056 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24056
                                        then
                                          match args with
                                          | (t,uu____24060)::[] ->
                                              let uu____24085 =
                                                let uu____24086 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24086.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24085 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24089::[],body,uu____24091)
                                                   ->
                                                   let uu____24126 =
                                                     simp_t body  in
                                                   (match uu____24126 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24132 -> tm1)
                                               | uu____24136 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24138))::(t,uu____24140)::[]
                                              ->
                                              let uu____24180 =
                                                let uu____24181 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24181.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24180 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24184::[],body,uu____24186)
                                                   ->
                                                   let uu____24221 =
                                                     simp_t body  in
                                                   (match uu____24221 with
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
                                                    | uu____24229 -> tm1)
                                               | uu____24233 -> tm1)
                                          | uu____24234 -> tm1
                                        else
                                          (let uu____24247 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24247
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24250;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24251;_},uu____24252)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24278;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24279;_},uu____24280)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24306 -> tm1
                                           else
                                             (let uu____24319 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____24319
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____24333 =
                                                    let uu____24334 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____24334.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____24333 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____24345 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24359 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____24359
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____24394 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____24394
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24400 =
                                                         let uu____24401 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____24401.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____24400 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24404 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24412 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24412
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24421
                                                                  =
                                                                  let uu____24422
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24422.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24421
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,uu____24428)
                                                                    -> hd
                                                                | uu____24453
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____24457
                                                                =
                                                                let uu____24468
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____24468]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24457)
                                                       | uu____24501 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24506 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____24506 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24526 ->
                                                     let uu____24535 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____24535 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24546 = simp_t t  in
                      (match uu____24546 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24555 ->
                      let uu____24578 = is_const_match tm1  in
                      (match uu____24578 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24587 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____24597  ->
               (let uu____24599 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24601 = FStar_Syntax_Print.term_to_string t  in
                let uu____24603 =
                  FStar_Util.string_of_int (FStar_List.length env1)  in
                let uu____24611 =
                  let uu____24613 =
                    let uu____24616 = firstn (Prims.of_int (4)) stack1  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24616
                     in
                  stack_to_string uu____24613  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24599 uu____24601 uu____24603 uu____24611);
               (let uu____24641 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24641
                then
                  let uu____24645 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24645 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24652 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24654 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24656 =
                          let uu____24658 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24658
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24652
                          uu____24654 uu____24656);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____24680 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack1 with
                | (Arg uu____24688)::uu____24689 -> true
                | uu____24699 -> false)
              in
           if uu____24680
           then
             let uu____24702 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____24702 (norm cfg env1 stack1)
           else
             (let t1 = maybe_simplify cfg env1 stack1 t  in
              match stack1 with
              | [] -> t1
              | (Debug (tm,time_then))::stack2 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____24716 =
                        let uu____24718 =
                          let uu____24720 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____24720  in
                        FStar_Util.string_of_int uu____24718  in
                      let uu____24727 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____24729 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                      let uu____24731 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____24716 uu____24727 uu____24729 uu____24731)
                   else ();
                   rebuild cfg env1 stack2 t1)
              | (Cfg cfg1)::stack2 -> rebuild cfg1 env1 stack2 t1
              | (Meta (uu____24740,m,r))::stack2 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env1 stack2 t2
              | (MemoLazy r)::stack2 ->
                  (set_memo cfg r (env1, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24769  ->
                        let uu____24770 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24770);
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
                  let uu____24813 =
                    let uu___2832_24814 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2832_24814.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2832_24814.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env1 stack2 uu____24813
              | (Arg (Univ uu____24817,uu____24818,uu____24819))::uu____24820
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____24824,uu____24825))::uu____24826 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env1 stack2 t2
              | (Arg
                  (Clos (env_arg,tm,uu____24842,uu____24843),aq,r))::stack2
                  when
                  let uu____24895 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24895 ->
                  let t2 =
                    let uu____24899 =
                      let uu____24904 =
                        let uu____24905 = closure_as_term cfg env_arg tm  in
                        (uu____24905, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____24904  in
                    uu____24899 FStar_Pervasives_Native.None r  in
                  rebuild cfg env1 stack2 t2
              | (Arg (Clos (env_arg,tm,m,uu____24915),aq,r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24970  ->
                        let uu____24971 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____24971);
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
                     (let uu____24991 = FStar_ST.op_Bang m  in
                      match uu____24991 with
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
                      | FStar_Pervasives_Native.Some (uu____25079,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack2 t2))
              | (App (env2,head,aq,r))::stack' when should_reify cfg stack1
                  ->
                  let t0 = t1  in
                  let fallback msg uu____25135 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____25140  ->
                         let uu____25141 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____25141);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env2 stack' t2)
                     in
                  let uu____25151 =
                    let uu____25152 = FStar_Syntax_Subst.compress t1  in
                    uu____25152.FStar_Syntax_Syntax.n  in
                  (match uu____25151 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env2 stack1 t2
                         m ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____25180 = closure_as_term cfg env2 ty  in
                         reify_lift cfg t2 msrc mtgt uu____25180  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____25184  ->
                             let uu____25185 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____25185);
                        (let uu____25188 = FStar_List.tl stack1  in
                         norm cfg env2 uu____25188 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____25189);
                          FStar_Syntax_Syntax.pos = uu____25190;
                          FStar_Syntax_Syntax.vars = uu____25191;_},(e,uu____25193)::[])
                       -> norm cfg env2 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____25232 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____25249 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____25249 with
                        | (hd,args) ->
                            let uu____25292 =
                              let uu____25293 = FStar_Syntax_Util.un_uinst hd
                                 in
                              uu____25293.FStar_Syntax_Syntax.n  in
                            (match uu____25292 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____25297 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____25297 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____25300;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____25301;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____25302;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____25304;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____25305;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____25306;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____25307;_}
                                      when (FStar_List.length args) = n ->
                                      norm cfg env2 stack' t1
                                  | uu____25343 -> fallback " (3)" ())
                             | uu____25347 -> fallback " (4)" ()))
                   | uu____25349 -> fallback " (2)" ())
              | (App (env2,head,aq,r))::stack2 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env2 stack2 t2
              | (CBVApp (env',head,aq,r))::stack2 ->
                  let uu____25372 =
                    let uu____25373 =
                      let uu____25374 =
                        let uu____25381 =
                          let uu____25382 =
                            let uu____25414 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env1, t1, uu____25414, false)  in
                          Clos uu____25382  in
                        (uu____25381, aq, (t1.FStar_Syntax_Syntax.pos))  in
                      Arg uu____25374  in
                    uu____25373 :: stack2  in
                  norm cfg env' uu____25372 head
              | (Match (env',branches1,cfg1,r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____25489  ->
                        let uu____25490 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____25490);
                   (let scrutinee_env = env1  in
                    let env2 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____25501 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25506  ->
                           let uu____25507 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____25509 =
                             let uu____25511 =
                               FStar_All.pipe_right branches1
                                 (FStar_List.map
                                    (fun uu____25541  ->
                                       match uu____25541 with
                                       | (p,uu____25552,uu____25553) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____25511
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____25507 uu____25509);
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
                                   (fun uu___16_25578  ->
                                      match uu___16_25578 with
                                      | FStar_TypeChecker_Env.InliningDelta 
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                           -> true
                                      | uu____25582 -> false))
                               in
                            let steps =
                              let uu___3009_25585 =
                                cfg1.FStar_TypeChecker_Cfg.steps  in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3009_25585.FStar_TypeChecker_Cfg.for_extraction)
                              }  in
                            let uu___3012_25592 = cfg1  in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3012_25592.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3012_25592.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3012_25592.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3012_25592.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3012_25592.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3012_25592.FStar_TypeChecker_Cfg.reifying)
                            })
                          in
                       let norm_or_whnf env3 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env3 t2
                         else norm cfg_exclude_zeta env3 [] t2  in
                       let rec norm_pat env3 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____25667 ->
                             (p, env3)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____25698 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25787  ->
                                       fun uu____25788  ->
                                         match (uu____25787, uu____25788)
                                         with
                                         | ((pats1,env4),(p1,b)) ->
                                             let uu____25938 =
                                               norm_pat env4 p1  in
                                             (match uu____25938 with
                                              | (p2,env5) ->
                                                  (((p2, b) :: pats1), env5)))
                                    ([], env3))
                                in
                             (match uu____25698 with
                              | (pats1,env4) ->
                                  ((let uu___3040_26108 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3040_26108.FStar_Syntax_Syntax.p)
                                    }), env4))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3044_26129 = x  in
                               let uu____26130 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3044_26129.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3044_26129.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26130
                               }  in
                             ((let uu___3047_26144 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3047_26144.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3051_26155 = x  in
                               let uu____26156 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3051_26155.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3051_26155.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26156
                               }  in
                             ((let uu___3054_26170 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3054_26170.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3060_26186 = x  in
                               let uu____26187 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3060_26186.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3060_26186.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26187
                               }  in
                             let t3 = norm_or_whnf env3 t2  in
                             ((let uu___3064_26202 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3064_26202.FStar_Syntax_Syntax.p)
                               }), env3)
                          in
                       let branches2 =
                         match env2 with
                         | [] when whnf -> branches1
                         | uu____26246 ->
                             FStar_All.pipe_right branches1
                               (FStar_List.map
                                  (fun branch  ->
                                     let uu____26276 =
                                       FStar_Syntax_Subst.open_branch branch
                                        in
                                     match uu____26276 with
                                     | (p,wopt,e) ->
                                         let uu____26296 = norm_pat env2 p
                                            in
                                         (match uu____26296 with
                                          | (p1,env3) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____26351 =
                                                      norm_or_whnf env3 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____26351
                                                 in
                                              let e1 = norm_or_whnf env3 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____26368 =
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
                         if uu____26368
                         then
                           norm
                             (let uu___3083_26375 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3085_26378 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.zeta_full =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.zeta_full);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3085_26378.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3083_26375.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3083_26375.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3083_26375.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3083_26375.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3083_26375.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3083_26375.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3083_26375.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3083_26375.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____26382 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches2)) r
                          in
                       rebuild cfg1 env2 stack2 uu____26382)
                       in
                    let rec is_cons head =
                      let uu____26408 =
                        let uu____26409 = FStar_Syntax_Subst.compress head
                           in
                        uu____26409.FStar_Syntax_Syntax.n  in
                      match uu____26408 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____26414) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____26419 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26421;
                            FStar_Syntax_Syntax.fv_delta = uu____26422;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26424;
                            FStar_Syntax_Syntax.fv_delta = uu____26425;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____26426);_}
                          -> true
                      | uu____26434 -> false  in
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
                      let uu____26603 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____26603 with
                      | (head,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____26700 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26742 ->
                                    let uu____26743 =
                                      let uu____26745 = is_cons head  in
                                      Prims.op_Negation uu____26745  in
                                    FStar_Util.Inr uu____26743)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____26774 =
                                 let uu____26775 =
                                   FStar_Syntax_Util.un_uinst head  in
                                 uu____26775.FStar_Syntax_Syntax.n  in
                               (match uu____26774 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26794 ->
                                    let uu____26795 =
                                      let uu____26797 = is_cons head  in
                                      Prims.op_Negation uu____26797  in
                                    FStar_Util.Inr uu____26795))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____26888)::rest_a,(p1,uu____26891)::rest_p)
                          ->
                          let uu____26950 = matches_pat t2 p1  in
                          (match uu____26950 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____27003 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____27126 = matches_pat scrutinee1 p1  in
                          (match uu____27126 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____27172  ->
                                     let uu____27173 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____27175 =
                                       let uu____27177 =
                                         FStar_List.map
                                           (fun uu____27189  ->
                                              match uu____27189 with
                                              | (uu____27195,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____27177
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____27173 uu____27175);
                                (let env0 = env2  in
                                 let env3 =
                                   FStar_List.fold_left
                                     (fun env3  ->
                                        fun uu____27231  ->
                                          match uu____27231 with
                                          | (bv,t2) ->
                                              let uu____27254 =
                                                let uu____27261 =
                                                  let uu____27264 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____27264
                                                   in
                                                let uu____27265 =
                                                  let uu____27266 =
                                                    let uu____27298 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____27298,
                                                      false)
                                                     in
                                                  Clos uu____27266  in
                                                (uu____27261, uu____27265)
                                                 in
                                              uu____27254 :: env3) env2 s
                                    in
                                 let uu____27391 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env3 stack2 uu____27391)))
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
            (fun uu____27424  ->
               let uu____27425 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____27425);
          (let uu____27428 = is_nbe_request s  in
           if uu____27428
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27434  ->
                   let uu____27435 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27435);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27441  ->
                   let uu____27442 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27442);
              (let uu____27445 =
                 FStar_Util.record_time (fun uu____27452  -> nbe_eval c s t)
                  in
               match uu____27445 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27461  ->
                         let uu____27462 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27464 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27462 uu____27464);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27472  ->
                   let uu____27473 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27473);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27479  ->
                   let uu____27480 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27480);
              (let uu____27483 =
                 FStar_Util.record_time (fun uu____27490  -> norm c [] [] t)
                  in
               match uu____27483 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27505  ->
                         let uu____27506 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27508 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27506 uu____27508);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27527 =
          let uu____27531 =
            let uu____27533 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____27533  in
          FStar_Pervasives_Native.Some uu____27531  in
        FStar_Profiling.profile
          (fun uu____27536  -> normalize_with_primitive_steps [] s e t)
          uu____27527 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____27558  ->
             let uu____27559 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27559);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27565  ->
             let uu____27566 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27566);
        (let uu____27569 =
           FStar_Util.record_time (fun uu____27576  -> norm_comp cfg [] c)
            in
         match uu____27569 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27591  ->
                   let uu____27592 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____27594 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27592
                     uu____27594);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env1  ->
    fun u  ->
      let uu____27608 = FStar_TypeChecker_Cfg.config [] env1  in
      norm_universe uu____27608 [] u
  
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
      let uu____27630 = normalize steps env1 t  in
      FStar_TypeChecker_Env.non_informative env1 uu____27630
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env1  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27642 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env1 t ->
          let uu___3253_27661 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3253_27661.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3253_27661.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env1
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27668 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env1 ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27668
          then
            let ct1 =
              let uu____27672 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27672 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____27679 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27679
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3263_27686 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3263_27686.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3263_27686.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3263_27686.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env1 c
                     in
                  let uu___3267_27688 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3267_27688.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3267_27688.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3267_27688.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3267_27688.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3270_27689 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3270_27689.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3270_27689.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27692 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env1  ->
    fun lc  ->
      let uu____27704 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env1 lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____27704
      then
        let uu____27707 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____27707 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3278_27711 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env1)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3278_27711.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3278_27711.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3278_27711.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env1  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3285_27730  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                   t) ()
        with
        | uu___3284_27733 ->
            ((let uu____27735 =
                let uu____27741 =
                  let uu____27743 = FStar_Util.message_of_exn uu___3284_27733
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27743
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27741)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27735);
             t)
         in
      FStar_Syntax_Print.term_to_string' env1.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env1  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3295_27762  ->
             match () with
             | () ->
                 let uu____27763 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                    in
                 norm_comp uu____27763 [] c) ()
        with
        | uu___3294_27772 ->
            ((let uu____27774 =
                let uu____27780 =
                  let uu____27782 = FStar_Util.message_of_exn uu___3294_27772
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27782
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27780)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27774);
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
                   let uu____27831 =
                     let uu____27832 =
                       let uu____27839 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27839)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27832  in
                   mk uu____27831 t01.FStar_Syntax_Syntax.pos
               | uu____27844 -> t2)
          | uu____27845 -> t2  in
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
        let uu____27939 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27939 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27952 ->
                 let uu____27953 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27953 with
                  | (actuals,uu____27963,uu____27964) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27984 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27984 with
                         | (binders,args) ->
                             let uu____27995 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27995
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
      | uu____28010 ->
          let uu____28011 = FStar_Syntax_Util.head_and_args t  in
          (match uu____28011 with
           | (head,args) ->
               let uu____28054 =
                 let uu____28055 = FStar_Syntax_Subst.compress head  in
                 uu____28055.FStar_Syntax_Syntax.n  in
               (match uu____28054 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____28076 =
                      let uu____28083 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____28083  in
                    (match uu____28076 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____28107 =
                              env1.FStar_TypeChecker_Env.type_of
                                (let uu___3365_28115 = env1  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3365_28115.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3365_28115.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3365_28115.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3365_28115.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3365_28115.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3365_28115.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3365_28115.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3365_28115.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3365_28115.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3365_28115.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3365_28115.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3365_28115.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3365_28115.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3365_28115.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3365_28115.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3365_28115.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3365_28115.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3365_28115.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3365_28115.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3365_28115.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3365_28115.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3365_28115.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3365_28115.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3365_28115.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3365_28115.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3365_28115.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3365_28115.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3365_28115.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3365_28115.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3365_28115.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3365_28115.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3365_28115.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3365_28115.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3365_28115.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3365_28115.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3365_28115.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3365_28115.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3365_28115.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3365_28115.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3365_28115.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3365_28115.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3365_28115.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3365_28115.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____28107 with
                            | (uu____28118,ty,uu____28120) ->
                                eta_expand_with_type env1 t ty))
                | uu____28121 ->
                    let uu____28122 =
                      env1.FStar_TypeChecker_Env.type_of
                        (let uu___3372_28130 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3372_28130.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3372_28130.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3372_28130.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3372_28130.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3372_28130.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3372_28130.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3372_28130.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3372_28130.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3372_28130.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3372_28130.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3372_28130.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3372_28130.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3372_28130.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3372_28130.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3372_28130.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3372_28130.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3372_28130.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3372_28130.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3372_28130.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3372_28130.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3372_28130.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3372_28130.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3372_28130.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3372_28130.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3372_28130.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3372_28130.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3372_28130.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3372_28130.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3372_28130.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3372_28130.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3372_28130.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3372_28130.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3372_28130.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3372_28130.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3372_28130.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3372_28130.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3372_28130.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3372_28130.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3372_28130.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3372_28130.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3372_28130.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3372_28130.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3372_28130.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____28122 with
                     | (uu____28133,ty,uu____28135) ->
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
      let uu___3384_28217 = x  in
      let uu____28218 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3384_28217.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3384_28217.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28218
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28221 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28237 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28238 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28239 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28240 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28247 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28248 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28249 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3410_28283 = rc  in
          let uu____28284 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28293 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3410_28283.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28284;
            FStar_Syntax_Syntax.residual_flags = uu____28293
          }  in
        let uu____28296 =
          let uu____28297 =
            let uu____28316 = elim_delayed_subst_binders bs  in
            let uu____28325 = elim_delayed_subst_term t2  in
            let uu____28328 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28316, uu____28325, uu____28328)  in
          FStar_Syntax_Syntax.Tm_abs uu____28297  in
        mk1 uu____28296
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28365 =
          let uu____28366 =
            let uu____28381 = elim_delayed_subst_binders bs  in
            let uu____28390 = elim_delayed_subst_comp c  in
            (uu____28381, uu____28390)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28366  in
        mk1 uu____28365
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28409 =
          let uu____28410 =
            let uu____28417 = elim_bv bv  in
            let uu____28418 = elim_delayed_subst_term phi  in
            (uu____28417, uu____28418)  in
          FStar_Syntax_Syntax.Tm_refine uu____28410  in
        mk1 uu____28409
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28449 =
          let uu____28450 =
            let uu____28467 = elim_delayed_subst_term t2  in
            let uu____28470 = elim_delayed_subst_args args  in
            (uu____28467, uu____28470)  in
          FStar_Syntax_Syntax.Tm_app uu____28450  in
        mk1 uu____28449
    | FStar_Syntax_Syntax.Tm_match (t2,branches1) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3432_28542 = p  in
              let uu____28543 =
                let uu____28544 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28544  in
              {
                FStar_Syntax_Syntax.v = uu____28543;
                FStar_Syntax_Syntax.p =
                  (uu___3432_28542.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3436_28546 = p  in
              let uu____28547 =
                let uu____28548 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28548  in
              {
                FStar_Syntax_Syntax.v = uu____28547;
                FStar_Syntax_Syntax.p =
                  (uu___3436_28546.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3442_28555 = p  in
              let uu____28556 =
                let uu____28557 =
                  let uu____28564 = elim_bv x  in
                  let uu____28565 = elim_delayed_subst_term t0  in
                  (uu____28564, uu____28565)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28557  in
              {
                FStar_Syntax_Syntax.v = uu____28556;
                FStar_Syntax_Syntax.p =
                  (uu___3442_28555.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3448_28590 = p  in
              let uu____28591 =
                let uu____28592 =
                  let uu____28606 =
                    FStar_List.map
                      (fun uu____28632  ->
                         match uu____28632 with
                         | (x,b) ->
                             let uu____28649 = elim_pat x  in
                             (uu____28649, b)) pats
                     in
                  (fv, uu____28606)  in
                FStar_Syntax_Syntax.Pat_cons uu____28592  in
              {
                FStar_Syntax_Syntax.v = uu____28591;
                FStar_Syntax_Syntax.p =
                  (uu___3448_28590.FStar_Syntax_Syntax.p)
              }
          | uu____28664 -> p  in
        let elim_branch uu____28688 =
          match uu____28688 with
          | (pat,wopt,t3) ->
              let uu____28714 = elim_pat pat  in
              let uu____28717 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28720 = elim_delayed_subst_term t3  in
              (uu____28714, uu____28717, uu____28720)
           in
        let uu____28725 =
          let uu____28726 =
            let uu____28749 = elim_delayed_subst_term t2  in
            let uu____28752 = FStar_List.map elim_branch branches1  in
            (uu____28749, uu____28752)  in
          FStar_Syntax_Syntax.Tm_match uu____28726  in
        mk1 uu____28725
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28883 =
          match uu____28883 with
          | (tc,topt) ->
              let uu____28918 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28928 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28928
                | FStar_Util.Inr c ->
                    let uu____28930 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28930
                 in
              let uu____28931 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28918, uu____28931)
           in
        let uu____28940 =
          let uu____28941 =
            let uu____28968 = elim_delayed_subst_term t2  in
            let uu____28971 = elim_ascription a  in
            (uu____28968, uu____28971, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28941  in
        mk1 uu____28940
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3478_29034 = lb  in
          let uu____29035 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____29038 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3478_29034.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3478_29034.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____29035;
            FStar_Syntax_Syntax.lbeff =
              (uu___3478_29034.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____29038;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3478_29034.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3478_29034.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____29041 =
          let uu____29042 =
            let uu____29056 =
              let uu____29064 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____29064)  in
            let uu____29076 = elim_delayed_subst_term t2  in
            (uu____29056, uu____29076)  in
          FStar_Syntax_Syntax.Tm_let uu____29042  in
        mk1 uu____29041
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____29121 =
          let uu____29122 =
            let uu____29129 = elim_delayed_subst_term tm  in
            (uu____29129, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____29122  in
        mk1 uu____29121
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29140 =
          let uu____29141 =
            let uu____29148 = elim_delayed_subst_term t2  in
            let uu____29151 = elim_delayed_subst_meta md  in
            (uu____29148, uu____29151)  in
          FStar_Syntax_Syntax.Tm_meta uu____29141  in
        mk1 uu____29140

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29160  ->
         match uu___17_29160 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29164 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29164
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
        let uu____29187 =
          let uu____29188 =
            let uu____29197 = elim_delayed_subst_term t  in
            (uu____29197, uopt)  in
          FStar_Syntax_Syntax.Total uu____29188  in
        mk1 uu____29187
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29214 =
          let uu____29215 =
            let uu____29224 = elim_delayed_subst_term t  in
            (uu____29224, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29215  in
        mk1 uu____29214
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3511_29233 = ct  in
          let uu____29234 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29237 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29248 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3511_29233.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3511_29233.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29234;
            FStar_Syntax_Syntax.effect_args = uu____29237;
            FStar_Syntax_Syntax.flags = uu____29248
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29251  ->
    match uu___18_29251 with
    | FStar_Syntax_Syntax.Meta_pattern (names,args) ->
        let uu____29286 =
          let uu____29307 = FStar_List.map elim_delayed_subst_term names  in
          let uu____29316 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29307, uu____29316)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29286
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____29371 =
          let uu____29378 = elim_delayed_subst_term t  in (m, uu____29378)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____29371
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____29390 =
          let uu____29399 = elim_delayed_subst_term t  in
          (m1, m2, uu____29399)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29390
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
      (fun uu____29432  ->
         match uu____29432 with
         | (t,q) ->
             let uu____29451 = elim_delayed_subst_term t  in (uu____29451, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29479  ->
         match uu____29479 with
         | (x,q) ->
             let uu____29498 =
               let uu___3537_29499 = x  in
               let uu____29500 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3537_29499.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3537_29499.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29500
               }  in
             (uu____29498, q)) bs

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
            | (uu____29608,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29640,FStar_Util.Inl t) ->
                let uu____29662 =
                  let uu____29669 =
                    let uu____29670 =
                      let uu____29685 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29685)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29670  in
                  FStar_Syntax_Syntax.mk uu____29669  in
                uu____29662 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29698 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29698 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env1 t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29730 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29803 ->
                    let uu____29804 =
                      let uu____29813 =
                        let uu____29814 = FStar_Syntax_Subst.compress t4  in
                        uu____29814.FStar_Syntax_Syntax.n  in
                      (uu____29813, tc)  in
                    (match uu____29804 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29843) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29890) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29935,FStar_Util.Inl uu____29936) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29967 -> failwith "Impossible")
                 in
              (match uu____29730 with
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
          let uu____30106 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inl t)  in
          match uu____30106 with
          | (univ_names1,binders1,tc) ->
              let uu____30180 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30180)
  
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
          let uu____30234 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inr c)  in
          match uu____30234 with
          | (univ_names1,binders1,tc) ->
              let uu____30308 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30308)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env1  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____30350 = elim_uvars_aux_t env1 univ_names binders typ  in
          (match uu____30350 with
           | (univ_names1,binders1,typ1) ->
               let uu___3620_30390 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3620_30390.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3620_30390.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3620_30390.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3620_30390.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3620_30390.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3626_30405 = s  in
          let uu____30406 =
            let uu____30407 =
              let uu____30416 = FStar_List.map (elim_uvars env1) sigs  in
              (uu____30416, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____30407  in
          {
            FStar_Syntax_Syntax.sigel = uu____30406;
            FStar_Syntax_Syntax.sigrng =
              (uu___3626_30405.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3626_30405.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3626_30405.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3626_30405.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3626_30405.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____30435 = elim_uvars_aux_t env1 univ_names [] typ  in
          (match uu____30435 with
           | (univ_names1,uu____30459,typ1) ->
               let uu___3640_30481 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3640_30481.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3640_30481.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3640_30481.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3640_30481.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3640_30481.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____30488 = elim_uvars_aux_t env1 univ_names [] typ  in
          (match uu____30488 with
           | (univ_names1,uu____30512,typ1) ->
               let uu___3651_30534 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3651_30534.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3651_30534.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3651_30534.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3651_30534.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3651_30534.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30564 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30564 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____30589 =
                            let uu____30590 =
                              let uu____30591 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env1 uu____30591  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30590
                             in
                          elim_delayed_subst_term uu____30589  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3667_30594 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3667_30594.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3667_30594.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3667_30594.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3667_30594.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3670_30595 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3670_30595.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3670_30595.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3670_30595.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3670_30595.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3670_30595.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____30604 = elim_uvars_aux_t env1 us [] t  in
          (match uu____30604 with
           | (us1,uu____30628,t1) ->
               let uu___3681_30650 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3681_30650.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3681_30650.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3681_30650.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3681_30650.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3681_30650.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30652 =
            elim_uvars_aux_t env1 ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____30652 with
           | (univs,binders,uu____30671) ->
               let uu____30692 =
                 let uu____30697 = FStar_Syntax_Subst.univ_var_opening univs
                    in
                 match uu____30697 with
                 | (univs_opening,univs1) ->
                     let uu____30720 =
                       FStar_Syntax_Subst.univ_var_closing univs1  in
                     (univs_opening, uu____30720)
                  in
               (match uu____30692 with
                | (univs_opening,univs_closing) ->
                    let uu____30723 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30729 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30730 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30729, uu____30730)  in
                    (match uu____30723 with
                     | (b_opening,b_closing) ->
                         let n = FStar_List.length univs  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30756 =
                           match uu____30756 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30774 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30774 with
                                | (us1,t1) ->
                                    let uu____30785 =
                                      let uu____30794 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30799 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30794, uu____30799)  in
                                    (match uu____30785 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30822 =
                                           let uu____30831 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____30836 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____30831, uu____30836)  in
                                         (match uu____30822 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30860 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30860
                                                 in
                                              let uu____30861 =
                                                elim_uvars_aux_t env1 [] []
                                                  t2
                                                 in
                                              (match uu____30861 with
                                               | (uu____30888,uu____30889,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30912 =
                                                       let uu____30913 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30913
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30912
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30922 =
                             elim_uvars_aux_t env1 univs binders t  in
                           match uu____30922 with
                           | (uu____30941,uu____30942,t1) -> t1  in
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
                             | uu____31018 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____31045 =
                               let uu____31046 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____31046.FStar_Syntax_Syntax.n  in
                             match uu____31045 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____31105 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31139 =
                               let uu____31140 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31140.FStar_Syntax_Syntax.n  in
                             match uu____31139 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31163) ->
                                 let uu____31188 = destruct_action_body body
                                    in
                                 (match uu____31188 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31237 ->
                                 let uu____31238 = destruct_action_body t  in
                                 (match uu____31238 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31293 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31293 with
                           | (action_univs,t) ->
                               let uu____31302 = destruct_action_typ_templ t
                                  in
                               (match uu____31302 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3765_31349 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3765_31349.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3765_31349.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3768_31351 = ed  in
                           let uu____31352 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____31353 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____31354 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3768_31351.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3768_31351.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31352;
                             FStar_Syntax_Syntax.combinators = uu____31353;
                             FStar_Syntax_Syntax.actions = uu____31354;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3768_31351.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3771_31357 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3771_31357.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3771_31357.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3771_31357.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3771_31357.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3771_31357.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31378 =
            match uu___19_31378 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____31409 = elim_uvars_aux_t env1 us [] t  in
                (match uu____31409 with
                 | (us1,uu____31441,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3786_31472 = sub_eff  in
            let uu____31473 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____31476 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3786_31472.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3786_31472.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31473;
              FStar_Syntax_Syntax.lift = uu____31476
            }  in
          let uu___3789_31479 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3789_31479.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3789_31479.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3789_31479.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3789_31479.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3789_31479.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____31489 = elim_uvars_aux_c env1 univ_names binders comp  in
          (match uu____31489 with
           | (univ_names1,binders1,comp1) ->
               let uu___3802_31529 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3802_31529.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3802_31529.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3802_31529.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3802_31529.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3802_31529.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31532 -> s
      | FStar_Syntax_Syntax.Sig_fail uu____31533 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31546 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n,p,(us_t,t),(us_ty,ty))
          ->
          let uu____31576 = elim_uvars_aux_t env1 us_t [] t  in
          (match uu____31576 with
           | (us_t1,uu____31600,t1) ->
               let uu____31622 = elim_uvars_aux_t env1 us_ty [] ty  in
               (match uu____31622 with
                | (us_ty1,uu____31646,ty1) ->
                    let uu___3829_31668 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3829_31668.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3829_31668.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3829_31668.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3829_31668.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3829_31668.FStar_Syntax_Syntax.sigopts)
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
        let uu____31719 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env1 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____31719 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____31741 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____31741 with
             | (uu____31748,head_def) ->
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
      let uu____31754 = FStar_Syntax_Util.head_and_args t  in
      match uu____31754 with
      | (head,args) ->
          let uu____31799 =
            let uu____31800 = FStar_Syntax_Subst.compress head  in
            uu____31800.FStar_Syntax_Syntax.n  in
          (match uu____31799 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31807;
                  FStar_Syntax_Syntax.vars = uu____31808;_},us)
               -> aux fv us args
           | uu____31814 -> FStar_Pervasives_Native.None)
  