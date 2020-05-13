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
  
let set_memo :
  'a . FStar_TypeChecker_Cfg.cfg -> 'a FStar_Syntax_Syntax.memo -> 'a -> unit
  =
  fun cfg  ->
    fun r  ->
      fun t  ->
        if cfg.FStar_TypeChecker_Cfg.memoize_lazy
        then
          let uu____1049 = FStar_ST.op_Bang r  in
          match uu____1049 with
          | FStar_Pervasives_Native.Some uu____1075 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (closure_to_string : closure -> Prims.string) =
  fun uu___1_1108  ->
    match uu___1_1108 with
    | Clos (env1,t,uu____1112,uu____1113) ->
        let uu____1160 =
          FStar_All.pipe_right (FStar_List.length env1)
            FStar_Util.string_of_int
           in
        let uu____1170 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1160 uu____1170
    | Univ uu____1173 -> "Univ"
    | Dummy  -> "dummy"
  
let (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env1  ->
    let uu____1199 =
      FStar_List.map
        (fun uu____1215  ->
           match uu____1215 with
           | (bopt,c) ->
               let uu____1229 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____1234 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____1229 uu____1234) env1
       in
    FStar_All.pipe_right uu____1199 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___2_1248  ->
    match uu___2_1248 with
    | Arg (c,uu____1251,uu____1252) ->
        let uu____1253 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1253
    | MemoLazy uu____1256 -> "MemoLazy"
    | Abs (uu____1264,bs,uu____1266,uu____1267,uu____1268) ->
        let uu____1273 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1273
    | UnivArgs uu____1284 -> "UnivArgs"
    | Match uu____1292 -> "Match"
    | App (uu____1302,t,uu____1304,uu____1305) ->
        let uu____1306 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1306
    | CBVApp (uu____1309,t,uu____1311,uu____1312) ->
        let uu____1313 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "CBVApp %s" uu____1313
    | Meta (uu____1316,m,uu____1318) -> "Meta"
    | Let uu____1320 -> "Let"
    | Cfg uu____1330 -> "Cfg"
    | Debug (t,uu____1333) ->
        let uu____1334 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1334
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1348 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1348 (FStar_String.concat "; ")
  
let is_empty : 'uuuuuu1363 . 'uuuuuu1363 Prims.list -> Prims.bool =
  fun uu___3_1371  ->
    match uu___3_1371 with | [] -> true | uu____1375 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env1  ->
    fun x  ->
      try
        (fun uu___119_1408  ->
           match () with
           | () ->
               let uu____1409 =
                 FStar_List.nth env1 x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1409) ()
      with
      | uu___118_1426 ->
          let uu____1427 =
            let uu____1429 = FStar_Syntax_Print.db_to_string x  in
            let uu____1431 = env_to_string env1  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1429
              uu____1431
             in
          failwith uu____1427
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____1442 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____1442
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1449 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____1449
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1456 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____1456
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
          let uu____1494 =
            FStar_List.fold_left
              (fun uu____1520  ->
                 fun u1  ->
                   match uu____1520 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1545 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1545 with
                        | (k_u,n) ->
                            let uu____1563 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1563
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1494 with
          | (uu____1584,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___153_1612  ->
                    match () with
                    | () ->
                        let uu____1615 =
                          let uu____1616 = FStar_List.nth env1 x  in
                          FStar_Pervasives_Native.snd uu____1616  in
                        (match uu____1615 with
                         | Univ u3 ->
                             ((let uu____1635 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____1635
                               then
                                 let uu____1640 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1640
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____1645 ->
                             let uu____1646 =
                               let uu____1648 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1648
                                in
                             failwith uu____1646)) ()
               with
               | uu____1658 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1664 =
                        let uu____1666 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____1666
                         in
                      failwith uu____1664))
          | FStar_Syntax_Syntax.U_unif uu____1671 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1682 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1693 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1700 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1700 norm_univs_for_max  in
              (match us1 with
               | u_k::hd::rest ->
                   let rest1 = hd :: rest  in
                   let uu____1717 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1717 with
                    | (FStar_Syntax_Syntax.U_zero ,n) ->
                        let uu____1728 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1738 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1738 with
                                  | (uu____1745,m) -> n <= m))
                           in
                        if uu____1728 then rest1 else us1
                    | uu____1754 -> us1)
               | uu____1760 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1764 = aux u3  in
              FStar_List.map
                (fun uu____1767  -> FStar_Syntax_Syntax.U_succ uu____1767)
                uu____1764
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1771 = aux u  in
           match uu____1771 with
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
            (fun uu____1932  ->
               let uu____1933 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1935 = env_to_string env1  in
               let uu____1937 = FStar_Syntax_Print.term_to_string t  in
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
                    let uu____1968 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env1 stack1 uu____1968
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_constant uu____1969 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_name uu____1970 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_lazy uu____1971 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_fvar uu____1972 ->
                    rebuild_closure cfg env1 stack1 t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1997 ->
                           let uu____2010 =
                             let uu____2012 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____2014 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____2012 uu____2014
                              in
                           failwith uu____2010
                       | uu____2019 -> inline_closure_env cfg env1 stack1 t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_2055  ->
                                         match uu___4_2055 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____2062 =
                                               let uu____2069 =
                                                 inline_closure_env cfg env1
                                                   [] t1
                                                  in
                                               (x, uu____2069)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____2062
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___247_2081 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___247_2081.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___247_2081.FStar_Syntax_Syntax.sort)
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
                                              | uu____2087 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____2090 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___256_2095 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___256_2095.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___256_2095.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____2116 =
                        let uu____2117 = norm_universe cfg env1 u  in
                        FStar_Syntax_Syntax.Tm_type uu____2117  in
                      FStar_Syntax_Syntax.mk uu____2116
                        t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____2125 =
                        FStar_List.map (norm_universe cfg env1) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2125  in
                    rebuild_closure cfg env1 stack1 t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____2127 = lookup_bvar env1 x  in
                    (match uu____2127 with
                     | Univ uu____2130 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___272_2135 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___272_2135.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___272_2135.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env1 stack1 t1
                     | Clos (env2,t0,uu____2141,uu____2142) ->
                         inline_closure_env cfg env2 stack1 t0)
                | FStar_Syntax_Syntax.Tm_app (head,args) ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____2233  ->
                              fun stack2  ->
                                match uu____2233 with
                                | (a,aq) ->
                                    let uu____2245 =
                                      let uu____2246 =
                                        let uu____2253 =
                                          let uu____2254 =
                                            let uu____2286 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env1, a, uu____2286, false)  in
                                          Clos uu____2254  in
                                        (uu____2253, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2246  in
                                    uu____2245 :: stack2) args)
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
                    let uu____2454 = close_binders cfg env1 bs  in
                    (match uu____2454 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env1 stack1 t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____2504) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env1 stack1
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2515 =
                      let uu____2528 =
                        let uu____2537 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2537]  in
                      close_binders cfg env1 uu____2528  in
                    (match uu____2515 with
                     | (x1,env2) ->
                         let phi1 = non_tail_inline_closure_env cfg env2 phi
                            in
                         let t1 =
                           let uu____2582 =
                             let uu____2583 =
                               let uu____2590 =
                                 let uu____2591 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2591
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2590, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2583  in
                           FStar_Syntax_Syntax.mk uu____2582
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env2 stack1 t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2690 =
                            non_tail_inline_closure_env cfg env1 t2  in
                          FStar_Util.Inl uu____2690
                      | FStar_Util.Inr c ->
                          let uu____2704 = close_comp cfg env1 c  in
                          FStar_Util.Inr uu____2704
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env1)
                       in
                    let t2 =
                      let uu____2723 =
                        let uu____2724 =
                          let uu____2751 =
                            non_tail_inline_closure_env cfg env1 t1  in
                          (uu____2751, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2724  in
                      FStar_Syntax_Syntax.mk uu____2723
                        t.FStar_Syntax_Syntax.pos
                       in
                    rebuild_closure cfg env1 stack1 t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2797 =
                            let uu____2798 =
                              let uu____2805 =
                                non_tail_inline_closure_env cfg env1 t'  in
                              (uu____2805, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2798  in
                          FStar_Syntax_Syntax.mk uu____2797
                            t.FStar_Syntax_Syntax.pos
                      | FStar_Syntax_Syntax.Quote_static  ->
                          let qi1 =
                            FStar_Syntax_Syntax.on_antiquoted
                              (non_tail_inline_closure_env cfg env1) qi
                             in
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_quoted (t', qi1))
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
                        (fun env2  -> fun uu____2860  -> dummy :: env2) env1
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
                    let uu____2881 =
                      let uu____2892 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2892
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2914 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___364_2930 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___364_2930.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___364_2930.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2914))
                       in
                    (match uu____2881 with
                     | (nm,body1) ->
                         let attrs =
                           FStar_List.map
                             (non_tail_inline_closure_env cfg env0)
                             lb.FStar_Syntax_Syntax.lbattrs
                            in
                         let lb1 =
                           let uu___370_2957 = lb  in
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
                           }  in
                         let t1 =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack1 t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2974,lbs),body) ->
                    let norm_one_lb env2 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____3040  -> fun env3  -> dummy :: env3)
                          lb.FStar_Syntax_Syntax.lbunivs env2
                         in
                      let env3 =
                        let uu____3057 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____3057
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____3072  -> fun env3  -> dummy :: env3)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____3096 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____3096
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___393_3107 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___393_3107.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___393_3107.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___396_3108 = lb  in
                      let uu____3109 =
                        non_tail_inline_closure_env cfg env3
                          lb.FStar_Syntax_Syntax.lbdef
                         in
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
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env1))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____3141  -> fun env2  -> dummy :: env2)
                          lbs1 env1
                         in
                      non_tail_inline_closure_env cfg body_env body  in
                    let t1 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_let ((true, lbs1), body1))
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
            (fun uu____3233  ->
               let uu____3234 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3236 = env_to_string env1  in
               let uu____3238 = stack_to_string stack1  in
               let uu____3240 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 ">>> %s (env=%s, stack=%s)\nRebuild closure_as_term %s\n"
                 uu____3234 uu____3236 uu____3238 uu____3240);
          (match stack1 with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3247,uu____3248),aq,r))::stack2 ->
               let stack3 = (App (env1, t, aq, r)) :: stack2  in
               inline_closure_env cfg env_arg stack3 tm
           | (App (env2,head,aq,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.extend_app head (t, aq) r  in
               rebuild_closure cfg env2 stack2 t1
           | (CBVApp (env2,head,aq,r))::stack2 ->
               let t1 = FStar_Syntax_Syntax.extend_app head (t, aq) r  in
               rebuild_closure cfg env2 stack2 t1
           | (Abs (env',bs,env'',lopt,r))::stack2 ->
               let uu____3339 = close_binders cfg env' bs  in
               (match uu____3339 with
                | (bs1,uu____3355) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3375 =
                      let uu___463_3378 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___463_3378.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___463_3378.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env1 stack2 uu____3375)
           | (Match (env2,branches1,cfg1,r))::stack2 ->
               let close_one_branch env3 uu____3434 =
                 match uu____3434 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env4 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3549 ->
                           (p, env4)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3580 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3669  ->
                                     fun uu____3670  ->
                                       match (uu____3669, uu____3670) with
                                       | ((pats1,env5),(p1,b)) ->
                                           let uu____3820 = norm_pat env5 p1
                                              in
                                           (match uu____3820 with
                                            | (p2,env6) ->
                                                (((p2, b) :: pats1), env6)))
                                  ([], env4))
                              in
                           (match uu____3580 with
                            | (pats1,env5) ->
                                ((let uu___500_3990 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___500_3990.FStar_Syntax_Syntax.p)
                                  }), env5))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___504_4011 = x  in
                             let uu____4012 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___504_4011.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___504_4011.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4012
                             }  in
                           ((let uu___507_4026 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___507_4026.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___511_4037 = x  in
                             let uu____4038 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___511_4037.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___511_4037.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4038
                             }  in
                           ((let uu___514_4052 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___514_4052.FStar_Syntax_Syntax.p)
                             }), (dummy :: env4))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___520_4068 = x  in
                             let uu____4069 =
                               non_tail_inline_closure_env cfg1 env4
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___520_4068.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___520_4068.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____4069
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env4 t1
                              in
                           ((let uu___524_4086 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___524_4086.FStar_Syntax_Syntax.p)
                             }), env4)
                        in
                     let uu____4091 = norm_pat env3 pat  in
                     (match uu____4091 with
                      | (pat1,env4) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____4160 =
                                  non_tail_inline_closure_env cfg1 env4 w  in
                                FStar_Pervasives_Native.Some uu____4160
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env4 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____4179 =
                   let uu____4180 =
                     let uu____4203 =
                       FStar_All.pipe_right branches1
                         (FStar_List.map (close_one_branch env2))
                        in
                     (t, uu____4203)  in
                   FStar_Syntax_Syntax.Tm_match uu____4180  in
                 FStar_Syntax_Syntax.mk uu____4179 t.FStar_Syntax_Syntax.pos
                  in
               rebuild_closure cfg1 env2 stack2 t1
           | (Meta (env_m,m,r))::stack2 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names,args) ->
                     let uu____4339 =
                       let uu____4360 =
                         FStar_All.pipe_right names
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m))
                          in
                       let uu____4377 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1  ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4486  ->
                                         match uu____4486 with
                                         | (a,q) ->
                                             let uu____4513 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a
                                                in
                                             (uu____4513, q)))))
                          in
                       (uu____4360, uu____4377)  in
                     FStar_Syntax_Syntax.Meta_pattern uu____4339
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4542 =
                       let uu____4549 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4549)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4542
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4561 =
                       let uu____4570 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4570)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4561
                 | uu____4575 -> m  in
               let t1 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (t, m1))
                   r
                  in
               rebuild_closure cfg env1 stack2 t1
           | uu____4581 -> failwith "Impossible: unexpected stack element")

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
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
            (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
            let uu____4597 =
              let uu____4598 =
                let uu____4599 = inline_closure_env cfg env1 [] t  in
                FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____4599  in
              FStar_Syntax_Syntax.Meta uu____4598  in
            FStar_Pervasives_Native.Some uu____4597
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
            (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
            let uu____4605 =
              let uu____4606 =
                let uu____4607 = inline_closure_env cfg env1 [] t  in
                FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____4607  in
              FStar_Syntax_Syntax.Meta uu____4606  in
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
  fun cfg  ->
    fun env1  ->
      fun bs  ->
        let uu____4624 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4708  ->
                  fun uu____4709  ->
                    match (uu____4708, uu____4709) with
                    | ((env2,out),(b,imp)) ->
                        let b1 =
                          let uu___584_4849 = b  in
                          let uu____4850 =
                            inline_closure_env cfg env2 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___584_4849.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___584_4849.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4850
                          }  in
                        let imp1 = close_imp cfg env2 imp  in
                        let env3 = dummy :: env2  in
                        (env3, ((b1, imp1) :: out))) (env1, []))
           in
        match uu____4624 with | (env2,bs1) -> ((FStar_List.rev bs1), env2)

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
        | uu____4992 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____5005 = inline_closure_env cfg env1 [] t  in
                 let uu____5006 =
                   FStar_Option.map (norm_universe cfg env1) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____5005 uu____5006
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5019 = inline_closure_env cfg env1 [] t  in
                 let uu____5020 =
                   FStar_Option.map (norm_universe cfg env1) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5019 uu____5020
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env1 []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5074  ->
                           match uu____5074 with
                           | (a,q) ->
                               let uu____5095 =
                                 inline_closure_env cfg env1 [] a  in
                               (uu____5095, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_5112  ->
                           match uu___5_5112 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5116 =
                                 inline_closure_env cfg env1 [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5116
                           | f -> f))
                    in
                 let uu____5120 =
                   let uu___617_5121 = c1  in
                   let uu____5122 =
                     FStar_List.map (norm_universe cfg env1)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5122;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___617_5121.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5120)

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
                   (fun uu___6_5140  ->
                      match uu___6_5140 with
                      | FStar_Syntax_Syntax.DECREASES uu____5142 -> false
                      | uu____5146 -> true))
               in
            let rc1 =
              let uu___629_5149 = rc  in
              let uu____5150 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env1 [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___629_5149.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5150;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5159 -> lopt

let (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___7_5180  ->
            match uu___7_5180 with
            | FStar_Syntax_Syntax.DECREASES uu____5182 -> false
            | uu____5186 -> true))
  
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
    let uu____5233 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____5233 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5272 = FStar_Syntax_Embeddings.unembed e t  in
        uu____5272 false FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
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
  fun cfg  ->
    fun env1  ->
      FStar_List.fold_right
        (fun uu____5354  ->
           fun subst  ->
             match uu____5354 with
             | (binder_opt,closure1) ->
                 (match (binder_opt, closure1) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env2,term,uu____5395,uu____5396)) ->
                      let uu____5457 = b  in
                      (match uu____5457 with
                       | (bv,uu____5465) ->
                           let uu____5466 =
                             let uu____5468 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5468  in
                           if uu____5466
                           then subst
                           else
                             (let term1 = closure_as_term cfg env2 term  in
                              let uu____5476 = unembed_binder term1  in
                              match uu____5476 with
                              | FStar_Pervasives_Native.None  -> subst
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5483 =
                                      let uu___669_5484 = bv  in
                                      let uu____5485 =
                                        FStar_Syntax_Subst.subst subst
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___669_5484.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___669_5484.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5485
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5483
                                     in
                                  let b_for_x =
                                    let uu____5491 =
                                      let uu____5498 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5498)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5491  in
                                  let subst1 =
                                    FStar_List.filter
                                      (fun uu___8_5514  ->
                                         match uu___8_5514 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5516,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5518;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5519;_})
                                             ->
                                             let uu____5524 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5524
                                         | uu____5526 -> true) subst
                                     in
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
  fun norm_cb  ->
    fun cfg  ->
      fun env1  ->
        fun tm  ->
          if
            Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
          then tm
          else
            (let uu____5602 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5602 with
             | (head,args) ->
                 let uu____5647 =
                   let uu____5648 = FStar_Syntax_Util.un_uinst head  in
                   uu____5648.FStar_Syntax_Syntax.n  in
                 (match uu____5647 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5654 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5654 with
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
                                (fun uu____5677  ->
                                   let uu____5678 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5680 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5682 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
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
                                    args
                                 in
                              match uu____5687 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5773  ->
                                        let uu____5774 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5774);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5779  ->
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
                                           (fun uu____5793  ->
                                              let uu____5794 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5794);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5802  ->
                                              let uu____5803 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5805 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5803 uu____5805);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5808 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5812  ->
                                 let uu____5813 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5813);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5819  ->
                            let uu____5820 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5820);
                       (match args with
                        | (a1,uu____5826)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5851 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5865  ->
                            let uu____5866 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5866);
                       (match args with
                        | (t,uu____5872)::(r,uu____5874)::[] ->
                            let uu____5915 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5915 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
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
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___757_5992 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___759_5995 = FStar_TypeChecker_Cfg.default_steps  in
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
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____6006 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____6017 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____6028 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd  ->
    fun args  ->
      let aux min_args =
        let uu____6049 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____6049
          (fun n  ->
             if n < min_args
             then Norm_request_none
             else
               if n = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____6081 =
        let uu____6082 = FStar_Syntax_Util.un_uinst hd  in
        uu____6082.FStar_Syntax_Syntax.n  in
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
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____6100 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____6100)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd  ->
    fun args  ->
      let uu____6113 =
        let uu____6114 = FStar_Syntax_Util.un_uinst hd  in
        uu____6114.FStar_Syntax_Syntax.n  in
      match uu____6113 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6172 = FStar_Syntax_Util.mk_app hd [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____6172 rest
           | uu____6199 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6239 = FStar_Syntax_Util.mk_app hd [t]  in
               FStar_Syntax_Util.mk_app uu____6239 rest
           | uu____6258 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____6332 = FStar_Syntax_Util.mk_app hd [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____6332 rest
           | uu____6367 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6369 ->
          let uu____6370 =
            let uu____6372 = FStar_Syntax_Print.term_to_string hd  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6372
             in
          failwith uu____6370
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6393  ->
    match uu___9_6393 with
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
        let uu____6400 =
          let uu____6403 =
            let uu____6404 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6404  in
          [uu____6403]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6400
    | FStar_Syntax_Embeddings.UnfoldFully names ->
        let uu____6412 =
          let uu____6415 =
            let uu____6416 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldFully uu____6416  in
          [uu____6415]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6412
    | FStar_Syntax_Embeddings.UnfoldAttr names ->
        let uu____6424 =
          let uu____6427 =
            let uu____6428 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6428  in
          [uu____6427]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6424
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s  ->
    let s1 = FStar_List.concatMap tr_norm_step s  in
    let add_exclude s2 z =
      let uu____6464 =
        FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2  in
      if uu____6464 then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2  in
    let s2 = FStar_TypeChecker_Env.Beta :: s1  in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta  in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota  in s4
  
let get_norm_request :
  'uuuuuu6489 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu6489) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6540 =
            let uu____6545 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6545 s  in
          match uu____6540 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6561 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6561
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
        | uu____6596::(tm,uu____6598)::[] ->
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
        | (tm,uu____6627)::[] ->
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
        | (steps,uu____6648)::uu____6649::(tm,uu____6651)::[] ->
            let uu____6672 =
              let uu____6677 = full_norm steps  in parse_steps uu____6677  in
            (match uu____6672 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s), tm))
        | uu____6707 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6739 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6746  ->
                    match uu___10_6746 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6748 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6750 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6754 -> true
                    | uu____6758 -> false))
             in
          if uu____6739
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6768  ->
             let uu____6769 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6769);
        (let tm_norm =
           let uu____6773 =
             let uu____6788 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6788.FStar_TypeChecker_Env.nbe  in
           uu____6773 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6792  ->
              let uu____6793 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6793);
         tm_norm)
  
let firstn :
  'uuuuuu6803 .
    Prims.int ->
      'uuuuuu6803 Prims.list ->
        ('uuuuuu6803 Prims.list * 'uuuuuu6803 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack1  ->
      let rec drop_irrel uu___11_6860 =
        match uu___11_6860 with
        | (MemoLazy uu____6865)::s -> drop_irrel s
        | (UnivArgs uu____6875)::s -> drop_irrel s
        | s -> s  in
      let uu____6888 = drop_irrel stack1  in
      match uu____6888 with
      | (App
          (uu____6892,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6893;
                        FStar_Syntax_Syntax.vars = uu____6894;_},uu____6895,uu____6896))::uu____6897
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6902 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6931) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6941) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6962  ->
                  match uu____6962 with
                  | (a,uu____6973) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6984 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____7001 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____7003 -> false
    | FStar_Syntax_Syntax.Tm_type uu____7017 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____7019 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____7021 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____7023 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____7025 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____7028 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____7036 -> false
    | FStar_Syntax_Syntax.Tm_let uu____7044 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____7059 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____7079 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____7095 -> true
    | FStar_Syntax_Syntax.Tm_match uu____7103 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7175  ->
                   match uu____7175 with
                   | (a,uu____7186) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7197) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____7296,args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7351  ->
                        match uu____7351 with
                        | (a,uu____7362) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7371,uu____7372,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7378,t') ->
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
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7407 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7418 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7429 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7440 -> false
  
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
            let uu____7473 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7473 with
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
              (fun uu____7672  ->
                 fun uu____7673  ->
                   match (uu____7672, uu____7673) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7779 =
            match uu____7779 with
            | (x,y,z) ->
                let uu____7799 = FStar_Util.string_of_bool x  in
                let uu____7801 = FStar_Util.string_of_bool y  in
                let uu____7803 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7799 uu____7801
                  uu____7803
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7831  ->
                    let uu____7832 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7834 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7832 uu____7834);
               if b then reif else no)
            else
              if
                (let uu____7849 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7849)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7854  ->
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
                          ((is_rec,uu____7889),uu____7890);
                        FStar_Syntax_Syntax.sigrng = uu____7891;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7893;
                        FStar_Syntax_Syntax.sigattrs = uu____7894;
                        FStar_Syntax_Syntax.sigopts = uu____7895;_},uu____7896),uu____7897),uu____7898,uu____7899,uu____7900)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8009  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____8011,uu____8012,uu____8013,uu____8014) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8081  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____8084),uu____8085);
                        FStar_Syntax_Syntax.sigrng = uu____8086;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____8088;
                        FStar_Syntax_Syntax.sigattrs = uu____8089;
                        FStar_Syntax_Syntax.sigopts = uu____8090;_},uu____8091),uu____8092),uu____8093,uu____8094,uu____8095)
                     when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8204  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8206,FStar_Pervasives_Native.Some
                    uu____8207,uu____8208,uu____8209) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8277  ->
                           let uu____8278 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8278);
                      (let uu____8281 =
                         let uu____8293 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8319 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8319
                            in
                         let uu____8331 =
                           let uu____8343 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8369 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8369
                              in
                           let uu____8385 =
                             let uu____8397 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8423 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8423
                                in
                             [uu____8397]  in
                           uu____8343 :: uu____8385  in
                         uu____8293 :: uu____8331  in
                       comb_or uu____8281))
                 | (uu____8471,uu____8472,FStar_Pervasives_Native.Some
                    uu____8473,uu____8474) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8542  ->
                           let uu____8543 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8543);
                      (let uu____8546 =
                         let uu____8558 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8584 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8584
                            in
                         let uu____8596 =
                           let uu____8608 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8634 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8634
                              in
                           let uu____8650 =
                             let uu____8662 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8688 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8688
                                in
                             [uu____8662]  in
                           uu____8608 :: uu____8650  in
                         uu____8558 :: uu____8596  in
                       comb_or uu____8546))
                 | (uu____8736,uu____8737,uu____8738,FStar_Pervasives_Native.Some
                    uu____8739) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8807  ->
                           let uu____8808 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8808);
                      (let uu____8811 =
                         let uu____8823 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8849 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8849
                            in
                         let uu____8861 =
                           let uu____8873 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8899 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8899
                              in
                           let uu____8915 =
                             let uu____8927 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8953 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8953
                                in
                             [uu____8927]  in
                           uu____8873 :: uu____8915  in
                         uu____8823 :: uu____8861  in
                       comb_or uu____8811))
                 | uu____9001 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____9047  ->
                           let uu____9048 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____9050 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____9052 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____9048 uu____9050 uu____9052);
                      (let uu____9055 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_9061  ->
                                 match uu___12_9061 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____9067 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____9067 l))
                          in
                       FStar_All.pipe_left yesno uu____9055)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____9083  ->
               let uu____9084 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____9086 =
                 let uu____9088 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____9088  in
               let uu____9089 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____9084 uu____9086 uu____9089);
          (match res with
           | (false ,uu____9092,uu____9093) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____9118 ->
               let uu____9128 =
                 let uu____9130 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9130
                  in
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
                    let uu___1168_9218 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1170_9221 = cfg.FStar_TypeChecker_Cfg.steps
                            in
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
                        let uu____9283 = push e t  in (UnivArgs (us, r)) ::
                          uu____9283
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9295 =
                      let uu____9296 =
                        let uu____9297 = FStar_Syntax_Syntax.lid_of_fv fv  in
                        FStar_Const.Const_reflect uu____9297  in
                      FStar_Syntax_Syntax.Tm_constant uu____9296  in
                    FStar_Syntax_Syntax.mk uu____9295 FStar_Range.dummyRange
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
    let uu____9363 =
      let uu____9364 = FStar_Syntax_Subst.compress t  in
      uu____9364.FStar_Syntax_Syntax.n  in
    match uu____9363 with
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____9395 =
          let uu____9396 = FStar_Syntax_Util.un_uinst hd  in
          uu____9396.FStar_Syntax_Syntax.n  in
        (match uu____9395 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9413 =
                 let uu____9420 =
                   let uu____9431 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9431 FStar_List.tl  in
                 FStar_All.pipe_right uu____9420 FStar_List.hd  in
               FStar_All.pipe_right uu____9413 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9530 -> FStar_Pervasives_Native.None)
    | uu____9531 -> FStar_Pervasives_Native.None
  
let (is_partial_primop_app :
  FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun cfg  ->
    fun t  ->
      let uu____9545 = FStar_Syntax_Util.head_and_args t  in
      match uu____9545 with
      | (hd,args) ->
          let uu____9589 =
            let uu____9590 = FStar_Syntax_Util.un_uinst hd  in
            uu____9590.FStar_Syntax_Syntax.n  in
          (match uu____9589 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu____9595 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                  in
               (match uu____9595 with
                | FStar_Pervasives_Native.Some prim_step ->
                    prim_step.FStar_TypeChecker_Cfg.arity >
                      (FStar_List.length args)
                | FStar_Pervasives_Native.None  -> false)
           | uu____9609 -> false)
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9889 ->
                   let uu____9904 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9904
               | uu____9907 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9917  ->
               let uu____9918 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9920 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9922 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9924 =
                 FStar_Util.string_of_int (FStar_List.length env1)  in
               let uu____9932 =
                 let uu____9934 =
                   let uu____9937 = firstn (Prims.of_int (4)) stack1  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9937
                    in
                 stack_to_string uu____9934  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9918 uu____9920 uu____9922 uu____9924 uu____9932);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9965  ->
               let uu____9966 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9966);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9972  ->
                     let uu____9973 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9973);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9976 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9980  ->
                     let uu____9981 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9981);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____9984 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9988  ->
                     let uu____9989 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9989);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9992 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9996  ->
                     let uu____9997 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9997);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____10000;
                 FStar_Syntax_Syntax.fv_delta = uu____10001;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____10005  ->
                     let uu____10006 = FStar_Syntax_Print.term_to_string t1
                        in
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
                  (fun uu____10021  ->
                     let uu____10022 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____10022);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____10028 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____10028 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level uu____10031)
                    when uu____10031 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____10035  ->
                          let uu____10036 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____10036);
                     rebuild cfg env1 stack1 t1)
                | uu____10039 ->
                    let uu____10042 =
                      decide_unfolding cfg env1 stack1
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____10042 with
                     | FStar_Pervasives_Native.Some (cfg1,stack2) ->
                         do_unfold_fv cfg1 env1 stack2 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env1 stack1 t1))
           | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
               let qi1 =
                 FStar_Syntax_Syntax.on_antiquoted (norm cfg env1 []) qi  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                   t1.FStar_Syntax_Syntax.pos
                  in
               let uu____10081 = closure_as_term cfg env1 t2  in
               rebuild cfg env1 stack1 uu____10081
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10109 = is_norm_request hd args  in
                  uu____10109 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____10115 = rejig_norm_request hd args  in
                 norm cfg env1 stack1 uu____10115))
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10143 = is_norm_request hd args  in
                  uu____10143 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1292_10150 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1294_10153 = cfg.FStar_TypeChecker_Cfg.steps
                           in
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
                   }  in
                 let uu____10160 =
                   get_norm_request cfg (norm cfg' env1 []) args  in
                 match uu____10160 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack2 =
                         FStar_All.pipe_right stack1
                           (FStar_List.fold_right
                              (fun uu____10196  ->
                                 fun stack2  ->
                                   match uu____10196 with
                                   | (a,aq) ->
                                       let uu____10208 =
                                         let uu____10209 =
                                           let uu____10216 =
                                             let uu____10217 =
                                               let uu____10249 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env1, a, uu____10249, false)
                                                in
                                             Clos uu____10217  in
                                           (uu____10216, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10209  in
                                       uu____10208 :: stack2) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10317  ->
                            let uu____10318 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10318);
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
                         let uu____10350 =
                           let uu____10352 =
                             let uu____10354 = FStar_Util.time_diff start fin
                                in
                             FStar_Pervasives_Native.snd uu____10354  in
                           FStar_Util.string_of_int uu____10352  in
                         let uu____10361 =
                           FStar_Syntax_Print.term_to_string tm'  in
                         let uu____10363 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                         let uu____10365 =
                           FStar_Syntax_Print.term_to_string tm_norm  in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____10350 uu____10361 uu____10363 uu____10365)
                      else ();
                      rebuild cfg env1 stack1 tm_norm)
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     let delta_level =
                       let uu____10385 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___13_10392  ->
                                 match uu___13_10392 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____10394 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____10396 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____10400 -> true
                                 | uu____10404 -> false))
                          in
                       if uu____10385
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let cfg'1 =
                       let uu___1332_10412 = cfg  in
                       let uu____10413 =
                         let uu___1334_10414 =
                           FStar_TypeChecker_Cfg.to_fsteps s  in
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
                         }  in
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
                       }  in
                     let stack' =
                       let tail = (Cfg cfg) :: stack1  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____10422 =
                           let uu____10423 =
                             let uu____10428 = FStar_Util.now ()  in
                             (tm, uu____10428)  in
                           Debug uu____10423  in
                         uu____10422 :: tail
                       else tail  in
                     norm cfg'1 env1 stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env1 u  in
               let uu____10433 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env1 stack1 uu____10433
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env1 stack1 t'
               else
                 (let us1 =
                    let uu____10444 =
                      let uu____10451 =
                        FStar_List.map (norm_universe cfg env1) us  in
                      (uu____10451, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10444  in
                  let stack2 = us1 :: stack1  in norm cfg env1 stack2 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10460 = lookup_bvar env1 x  in
               (match uu____10460 with
                | Univ uu____10461 ->
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
                      let uu____10515 = FStar_ST.op_Bang r  in
                      (match uu____10515 with
                       | FStar_Pervasives_Native.Some (env3,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10611  ->
                                 let uu____10612 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10614 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10612
                                   uu____10614);
                            (let uu____10617 = maybe_weakly_reduced t'  in
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
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env2 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env2 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____10664)::uu____10665 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10676,uu____10677))::stack_rest ->
                    (match c with
                     | Univ uu____10681 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env1)
                           stack_rest t1
                     | uu____10690 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10720  ->
                                    let uu____10721 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10721);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env1) stack_rest body)
                          | b::tl ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10757  ->
                                    let uu____10758 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10758);
                               (let body1 =
                                  FStar_Syntax_Syntax.mk
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
                       (fun uu____10806  ->
                          let uu____10807 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10807);
                     norm cfg env1 stack2 t1)
                | (Match uu____10810)::uu____10811 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10826 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10826 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____10862  -> dummy :: env2) env1)
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
                                          let uu____10906 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10906)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_10914 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_10914.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_10914.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10915 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10921  ->
                                 let uu____10922 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10922);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1463_10937 = cfg  in
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
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Debug uu____10941)::uu____10942 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10953 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10953 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____10989  -> dummy :: env2) env1)
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
                                          let uu____11033 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11033)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11041 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11041.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11041.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11042 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11048  ->
                                 let uu____11049 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11049);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1463_11064 = cfg  in
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
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____11068)::uu____11069 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11082 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11082 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11118  -> dummy :: env2) env1)
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
                                          let uu____11162 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11162)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11170 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11170.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11170.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11171 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11177  ->
                                 let uu____11178 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11178);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1463_11193 = cfg  in
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
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11197)::uu____11198 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11213 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11213 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11249  -> dummy :: env2) env1)
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
                                          let uu____11293 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11293)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11301 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11301.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11301.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11302 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11308  ->
                                 let uu____11309 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11309);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1463_11324 = cfg  in
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
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11328)::uu____11329 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11344 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11344 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11380  -> dummy :: env2) env1)
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
                                          let uu____11424 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11424)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11432 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11432.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11432.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11433 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11439  ->
                                 let uu____11440 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11440);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1463_11455 = cfg  in
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
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (CBVApp uu____11459)::uu____11460 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11475 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11475 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11511  -> dummy :: env2) env1)
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
                                          let uu____11555 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11555)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11563 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11563.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11563.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11564 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11570  ->
                                 let uu____11571 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11571);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1463_11586 = cfg  in
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
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____11590)::uu____11591 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11610 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11610 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11646  -> dummy :: env2) env1)
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
                                          let uu____11690 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11690)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11698 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11698.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11698.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11699 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11705  ->
                                 let uu____11706 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11706);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1463_11721 = cfg  in
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
                      (let uu____11729 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11729 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11765  -> dummy :: env2) env1)
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
                                          let uu____11809 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11809)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1456_11817 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1456_11817.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1456_11817.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11818 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11824  ->
                                 let uu____11825 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11825);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1463_11840 = cfg  in
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
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head,args) ->
               let strict_args =
                 let uu____11876 =
                   let uu____11877 = FStar_Syntax_Util.un_uinst head  in
                   uu____11877.FStar_Syntax_Syntax.n  in
                 match uu____11876 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11886 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____11907  ->
                              fun stack2  ->
                                match uu____11907 with
                                | (a,aq) ->
                                    let uu____11919 =
                                      let uu____11920 =
                                        let uu____11927 =
                                          let uu____11928 =
                                            let uu____11960 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env1, a, uu____11960, false)  in
                                          Clos uu____11928  in
                                        (uu____11927, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11920  in
                                    uu____11919 :: stack2) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12028  ->
                          let uu____12029 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____12029);
                     norm cfg env1 stack2 head)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____12080  ->
                              match uu____12080 with
                              | (a,i) ->
                                  let uu____12091 = norm cfg env1 [] a  in
                                  (uu____12091, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____12097 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____12112 = FStar_List.nth norm_args i
                                    in
                                 match uu____12112 with
                                 | (arg_i,uu____12123) ->
                                     let uu____12124 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____12124 with
                                      | (head1,uu____12143) ->
                                          let uu____12168 =
                                            let uu____12169 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____12169.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____12168 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____12173 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____12176 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____12176
                                           | uu____12177 -> false)))))
                       in
                    if uu____12097
                    then
                      let stack2 =
                        FStar_All.pipe_right stack1
                          (FStar_List.fold_right
                             (fun uu____12194  ->
                                fun stack2  ->
                                  match uu____12194 with
                                  | (a,aq) ->
                                      let uu____12206 =
                                        let uu____12207 =
                                          let uu____12214 =
                                            let uu____12215 =
                                              let uu____12247 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env1, a, uu____12247, false)
                                               in
                                            Clos uu____12215  in
                                          (uu____12214, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____12207  in
                                      uu____12206 :: stack2) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12329  ->
                            let uu____12330 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12330);
                       norm cfg env1 stack2 head)
                    else
                      (let head1 = closure_as_term cfg env1 head  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head1 norm_args
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env1 stack1 term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12348) when
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
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_refine
                             ((let uu___1525_12393 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1525_12393.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1525_12393.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env1 stack1 t2
                  | uu____12394 ->
                      let uu____12409 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 uu____12409)
               else
                 (let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12413 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12413 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env1) [] f1  in
                      let t2 =
                        let uu____12444 =
                          let uu____12445 =
                            let uu____12452 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1534_12458 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1534_12458.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1534_12458.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12452)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12445  in
                        FStar_Syntax_Syntax.mk uu____12444
                          t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12482 = closure_as_term cfg env1 t1  in
                 rebuild cfg env1 stack1 uu____12482
               else
                 (let uu____12485 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12485 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12493 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env2  ->
                                  fun uu____12519  -> dummy :: env2) env1)
                           in
                        norm_comp cfg uu____12493 c1  in
                      let t2 =
                        let uu____12543 = norm_binders cfg env1 bs1  in
                        FStar_Syntax_Util.arrow uu____12543 c2  in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env1 stack1 t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12656)::uu____12657 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12670  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (Arg uu____12672)::uu____12673 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12684  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (App
                    (uu____12686,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12687;
                                   FStar_Syntax_Syntax.vars = uu____12688;_},uu____12689,uu____12690))::uu____12691
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12698  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (MemoLazy uu____12700)::uu____12701 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12712  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | uu____12714 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12717  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env1 [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12722  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12748 = norm cfg env1 [] t2  in
                             FStar_Util.Inl uu____12748
                         | FStar_Util.Inr c ->
                             let uu____12762 = norm_comp cfg env1 c  in
                             FStar_Util.Inr uu____12762
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env1 [])  in
                       match stack1 with
                       | (Cfg cfg1)::stack2 ->
                           let t2 =
                             let uu____12785 =
                               let uu____12786 =
                                 let uu____12813 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12813, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12786
                                in
                             FStar_Syntax_Syntax.mk uu____12785
                               t1.FStar_Syntax_Syntax.pos
                              in
                           norm cfg1 env1 stack2 t2
                       | uu____12848 ->
                           let uu____12849 =
                             let uu____12850 =
                               let uu____12851 =
                                 let uu____12878 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12878, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12851
                                in
                             FStar_Syntax_Syntax.mk uu____12850
                               t1.FStar_Syntax_Syntax.pos
                              in
                           rebuild cfg env1 stack1 uu____12849))))
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
                   let uu___1613_12956 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1615_12959 = cfg.FStar_TypeChecker_Cfg.steps
                           in
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
                         let uu____13000 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____13000 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1628_13020 = cfg  in
                               let uu____13021 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
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
                               }  in
                             let norm1 t2 =
                               let uu____13028 =
                                 let uu____13029 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env1 [] uu____13029  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____13028
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1635_13032 = lb  in
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
                             }))
                  in
               let uu____13033 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env1 stack1 uu____13033
           | FStar_Syntax_Syntax.Tm_let
               ((uu____13046,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____13047;
                               FStar_Syntax_Syntax.lbunivs = uu____13048;
                               FStar_Syntax_Syntax.lbtyp = uu____13049;
                               FStar_Syntax_Syntax.lbeff = uu____13050;
                               FStar_Syntax_Syntax.lbdef = uu____13051;
                               FStar_Syntax_Syntax.lbattrs = uu____13052;
                               FStar_Syntax_Syntax.lbpos = uu____13053;_}::uu____13054),uu____13055)
               -> rebuild cfg env1 stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let uu____13100 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
               if uu____13100
               then
                 let binder =
                   let uu____13104 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13104  in
                 let def =
                   FStar_Syntax_Util.unmeta_lift lb.FStar_Syntax_Syntax.lbdef
                    in
                 let env2 =
                   let uu____13115 =
                     let uu____13122 =
                       let uu____13123 =
                         let uu____13155 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env1, def, uu____13155, false)  in
                       Clos uu____13123  in
                     ((FStar_Pervasives_Native.Some binder), uu____13122)  in
                   uu____13115 :: env1  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____13230  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env2 stack1 body)
               else
                 (let uu____13234 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu____13237 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff
                          in
                       FStar_Syntax_Util.is_div_effect uu____13237)
                     in
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
                                  FStar_Util.left
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____13278  in
                            [uu____13271]  in
                          (uu____13262, body, FStar_Pervasives_Native.None)
                           in
                        FStar_Syntax_Syntax.Tm_abs uu____13243  in
                      FStar_Syntax_Syntax.mk uu____13242
                        t1.FStar_Syntax_Syntax.pos
                       in
                    let stack2 =
                      (CBVApp
                         (env1, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack1  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____13312  ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env1 stack2 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____13319  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____13321 = closure_as_term cfg env1 t1  in
                        rebuild cfg env1 stack1 uu____13321))
                    else
                      (let uu____13324 =
                         let uu____13329 =
                           let uu____13330 =
                             let uu____13337 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____13337
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____13330]  in
                         FStar_Syntax_Subst.open_term uu____13329 body  in
                       match uu____13324 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____13364  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____13373 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____13373  in
                               FStar_Util.Inl
                                 (let uu___1682_13389 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1682_13389.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1682_13389.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____13392  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1687_13395 = lb  in
                                let uu____13396 =
                                  norm cfg env1 []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____13399 =
                                  FStar_List.map (norm cfg env1 [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
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
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____13434  -> dummy :: env2)
                                     env1)
                                 in
                              let stack2 = (Cfg cfg) :: stack1  in
                              let cfg1 =
                                let uu___1694_13459 = cfg  in
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
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____13463  ->
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
               let uu____13484 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13484 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp
                              in
                           let lbname =
                             let uu____13520 =
                               let uu___1710_13521 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1710_13521.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1710_13521.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13520  in
                           let uu____13522 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13522 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env1 xs  in
                               let env2 =
                                 let uu____13548 =
                                   FStar_List.map (fun uu____13570  -> dummy)
                                     xs1
                                    in
                                 let uu____13577 =
                                   let uu____13586 =
                                     FStar_List.map
                                       (fun uu____13602  -> dummy) lbs1
                                      in
                                   FStar_List.append uu____13586 env1  in
                                 FStar_List.append uu____13548 uu____13577
                                  in
                               let def_body1 = norm cfg env2 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13622 =
                                       let uu___1724_13623 = rc  in
                                       let uu____13624 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env2 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1724_13623.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13624;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1724_13623.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13622
                                 | uu____13633 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1729_13639 = lb  in
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
                               }) lbs1
                       in
                    let env' =
                      let uu____13649 =
                        FStar_List.map (fun uu____13665  -> dummy) lbs2  in
                      FStar_List.append uu____13649 env1  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13673 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13673 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1738_13689 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1738_13689.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1738_13689.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env1 stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu____13723 = closure_as_term cfg env1 t1  in
               rebuild cfg env1 stack1 uu____13723
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13744 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13822  ->
                        match uu____13822 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1754_13947 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1754_13947.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1754_13947.FStar_Syntax_Syntax.sort)
                              }  in
                            let f_i = FStar_Syntax_Syntax.bv_to_tm bv  in
                            let fix_f_i =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
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
               (match uu____13744 with
                | (rec_env,memos,uu____14138) ->
                    let uu____14193 =
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
                             let uu____14442 =
                               let uu____14449 =
                                 let uu____14450 =
                                   let uu____14482 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14482, false)
                                    in
                                 Clos uu____14450  in
                               (FStar_Pervasives_Native.None, uu____14449)
                                in
                             uu____14442 :: env2)
                        (FStar_Pervasives_Native.snd lbs) env1
                       in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14567  ->
                     let uu____14568 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14568);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
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
                                 (l,r,uu____14602) ->
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
                             | uu____14681 -> norm cfg env1 stack1 head)
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
                                  let uu____14729 =
                                    let uu____14750 =
                                      norm_pattern_args cfg env1 args  in
                                    (names1, uu____14750)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14729
                              | uu____14779 -> m  in
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (head1, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env1 stack1 t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14785 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env1 stack1 t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14801 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14815 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14829 =
                        let uu____14831 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14833 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14831 uu____14833
                         in
                      failwith uu____14829
                    else
                      (let uu____14838 = inline_closure_env cfg env1 [] t2
                          in
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
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun t0  ->
          fun qninfo  ->
            fun f  ->
              let uu____14848 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14848 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14862  ->
                        let uu____14863 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14863);
                   rebuild cfg env1 stack1 t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14876  ->
                        let uu____14877 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14879 = FStar_Syntax_Print.term_to_string t
                           in
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
                          t0.FStar_Syntax_Syntax.pos t
                       in
                    let n = FStar_List.length us  in
                    if n > Prims.int_zero
                    then
                      match stack1 with
                      | (UnivArgs (us',uu____14892))::stack2 ->
                          ((let uu____14901 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14901
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14909 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14909) us'
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
                      | uu____14945 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env1 stack1 t1
                      | uu____14948 ->
                          let uu____14951 =
                            let uu____14953 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14953
                             in
                          failwith uu____14951
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
                    FStar_TypeChecker_Env.Inlining]  in
                  let cfg' =
                    let uu___1865_14991 = cfg  in
                    let uu____14992 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps
                       in
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
                    }  in
                  (cfg', ((Cfg cfg) :: stack1))
                else (cfg, stack1)  in
              match uu____14973 with
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
                     (uu____15033,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____15034;
                                    FStar_Syntax_Syntax.vars = uu____15035;_},uu____15036,uu____15037))::uu____15038
                     -> ()
                 | uu____15043 ->
                     let uu____15046 =
                       let uu____15048 = stack_to_string stack1  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____15048
                        in
                     failwith uu____15046);
                (let top0 = top  in
                 let top1 = FStar_Syntax_Util.unascribe top  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____15057  ->
                      let uu____15058 = FStar_Syntax_Print.tag_of_term top1
                         in
                      let uu____15060 =
                        FStar_Syntax_Print.term_to_string top1  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____15058
                        uu____15060);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1  in
                  let uu____15064 =
                    let uu____15065 = FStar_Syntax_Subst.compress top2  in
                    uu____15065.FStar_Syntax_Syntax.n  in
                  match uu____15064 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m
                         in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name
                         in
                      let uu____15087 =
                        let uu____15096 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr
                           in
                        FStar_All.pipe_right uu____15096 FStar_Util.must  in
                      (match uu____15087 with
                       | (uu____15111,repr) ->
                           let uu____15121 =
                             let uu____15128 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr
                                in
                             FStar_All.pipe_right uu____15128 FStar_Util.must
                              in
                           (match uu____15121 with
                            | (uu____15165,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15171 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15182 =
                                         let uu____15183 =
                                           FStar_Syntax_Subst.compress e  in
                                         uu____15183.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15182 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15189,uu____15190))
                                           ->
                                           let uu____15199 =
                                             let uu____15200 =
                                               FStar_Syntax_Subst.compress e1
                                                in
                                             uu____15200.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____15199 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15206,msrc,uu____15208))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15217 =
                                                  FStar_Syntax_Subst.compress
                                                    e2
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____15217
                                            | uu____15218 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15219 ->
                                           FStar_Pervasives_Native.None
                                        in
                                     let uu____15220 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     (match uu____15220 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___1944_15225 = lb  in
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
                                            }  in
                                          let uu____15226 =
                                            FStar_List.tl stack1  in
                                          let uu____15227 =
                                            let uu____15228 =
                                              let uu____15229 =
                                                let uu____15243 =
                                                  FStar_Syntax_Util.mk_reify
                                                    body
                                                   in
                                                ((false, [lb1]), uu____15243)
                                                 in
                                              FStar_Syntax_Syntax.Tm_let
                                                uu____15229
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____15228
                                              top2.FStar_Syntax_Syntax.pos
                                             in
                                          norm cfg env1 uu____15226
                                            uu____15227
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15259 =
                                            let uu____15261 = is_return body
                                               in
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
                                            | uu____15270 -> false  in
                                          if uu____15259
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
                                             let uu____15285 =
                                               let bv =
                                                 FStar_Syntax_Syntax.new_bv
                                                   FStar_Pervasives_Native.None
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let lb1 =
                                                 let uu____15294 =
                                                   let uu____15297 =
                                                     let uu____15308 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         x.FStar_Syntax_Syntax.sort
                                                        in
                                                     [uu____15308]  in
                                                   FStar_Syntax_Util.mk_app
                                                     repr uu____15297
                                                    in
                                                 let uu____15333 =
                                                   let uu____15334 =
                                                     FStar_TypeChecker_Env.is_total_effect
                                                       cfg.FStar_TypeChecker_Cfg.tcenv
                                                       eff_name
                                                      in
                                                   if uu____15334
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
                                                     = uu____15294;
                                                   FStar_Syntax_Syntax.lbeff
                                                     = uu____15333;
                                                   FStar_Syntax_Syntax.lbdef
                                                     = head;
                                                   FStar_Syntax_Syntax.lbattrs
                                                     = [];
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (head.FStar_Syntax_Syntax.pos)
                                                 }  in
                                               let uu____15341 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   bv
                                                  in
                                               (lb1, bv, uu____15341)  in
                                             match uu____15285 with
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
                                                   let uu____15358 =
                                                     let uu____15359 =
                                                       let uu____15378 =
                                                         let uu____15387 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             x
                                                            in
                                                         [uu____15387]  in
                                                       (uu____15378, body1,
                                                         (FStar_Pervasives_Native.Some
                                                            body_rc))
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____15359
                                                      in
                                                   FStar_Syntax_Syntax.mk
                                                     uu____15358
                                                     body1.FStar_Syntax_Syntax.pos
                                                    in
                                                 let close =
                                                   closure_as_term cfg env1
                                                    in
                                                 let bind_inst =
                                                   let uu____15426 =
                                                     let uu____15427 =
                                                       FStar_Syntax_Subst.compress
                                                         bind_repr
                                                        in
                                                     uu____15427.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____15426 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (bind,uu____15433::uu____15434::[])
                                                       ->
                                                       let uu____15439 =
                                                         let uu____15440 =
                                                           let uu____15447 =
                                                             let uu____15448
                                                               =
                                                               let uu____15449
                                                                 =
                                                                 close
                                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                                  in
                                                               (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                                 uu____15449
                                                                in
                                                             let uu____15450
                                                               =
                                                               let uu____15453
                                                                 =
                                                                 let uu____15454
                                                                   = 
                                                                   close t
                                                                    in
                                                                 (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                                   uu____15454
                                                                  in
                                                               [uu____15453]
                                                                in
                                                             uu____15448 ::
                                                               uu____15450
                                                              in
                                                           (bind,
                                                             uu____15447)
                                                            in
                                                         FStar_Syntax_Syntax.Tm_uinst
                                                           uu____15440
                                                          in
                                                       FStar_Syntax_Syntax.mk
                                                         uu____15439 rng
                                                   | uu____15457 ->
                                                       failwith
                                                         "NIY : Reification of indexed effects"
                                                    in
                                                 let maybe_range_arg =
                                                   let uu____15472 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____15472
                                                   then
                                                     let uu____15485 =
                                                       let uu____15494 =
                                                         FStar_TypeChecker_Cfg.embed_simple
                                                           FStar_Syntax_Embeddings.e_range
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                          in
                                                       FStar_Syntax_Syntax.as_arg
                                                         uu____15494
                                                        in
                                                     let uu____15495 =
                                                       let uu____15506 =
                                                         let uu____15515 =
                                                           FStar_TypeChecker_Cfg.embed_simple
                                                             FStar_Syntax_Embeddings.e_range
                                                             body2.FStar_Syntax_Syntax.pos
                                                             body2.FStar_Syntax_Syntax.pos
                                                            in
                                                         FStar_Syntax_Syntax.as_arg
                                                           uu____15515
                                                          in
                                                       [uu____15506]  in
                                                     uu____15485 ::
                                                       uu____15495
                                                   else []  in
                                                 let reified =
                                                   let args =
                                                     let uu____15564 =
                                                       FStar_Syntax_Util.is_layered
                                                         ed
                                                        in
                                                     if uu____15564
                                                     then
                                                       let unit_args =
                                                         let uu____15588 =
                                                           let uu____15589 =
                                                             let uu____15592
                                                               =
                                                               let uu____15593
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15593
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15592
                                                               FStar_Syntax_Subst.compress
                                                              in
                                                           uu____15589.FStar_Syntax_Syntax.n
                                                            in
                                                         match uu____15588
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_arrow
                                                             (uu____15634::uu____15635::bs,uu____15637)
                                                             when
                                                             (FStar_List.length
                                                                bs)
                                                               >=
                                                               (Prims.of_int (2))
                                                             ->
                                                             let uu____15689
                                                               =
                                                               let uu____15698
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   bs
                                                                   (FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2))))
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15698
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15689
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____15829
                                                                     ->
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.unit_const))
                                                         | uu____15836 ->
                                                             let uu____15837
                                                               =
                                                               let uu____15843
                                                                 =
                                                                 let uu____15845
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    ed.FStar_Syntax_Syntax.mname
                                                                    in
                                                                 let uu____15847
                                                                   =
                                                                   let uu____15849
                                                                    =
                                                                    let uu____15850
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    ed
                                                                    FStar_Syntax_Util.get_bind_vc_combinator
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15850
                                                                    FStar_Pervasives_Native.snd
                                                                     in
                                                                   FStar_All.pipe_right
                                                                    uu____15849
                                                                    FStar_Syntax_Print.term_to_string
                                                                    in
                                                                 FStar_Util.format2
                                                                   "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                                   uu____15845
                                                                   uu____15847
                                                                  in
                                                               (FStar_Errors.Fatal_UnexpectedEffect,
                                                                 uu____15843)
                                                                in
                                                             FStar_Errors.raise_error
                                                               uu____15837
                                                               rng
                                                          in
                                                       let uu____15884 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let uu____15893 =
                                                         let uu____15904 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t
                                                            in
                                                         let uu____15913 =
                                                           let uu____15924 =
                                                             let uu____15935
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head1
                                                                in
                                                             let uu____15944
                                                               =
                                                               let uu____15955
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   body2
                                                                  in
                                                               [uu____15955]
                                                                in
                                                             uu____15935 ::
                                                               uu____15944
                                                              in
                                                           FStar_List.append
                                                             unit_args
                                                             uu____15924
                                                            in
                                                         uu____15904 ::
                                                           uu____15913
                                                          in
                                                       uu____15884 ::
                                                         uu____15893
                                                     else
                                                       (let uu____16014 =
                                                          let uu____16025 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              lb.FStar_Syntax_Syntax.lbtyp
                                                             in
                                                          let uu____16034 =
                                                            let uu____16045 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t
                                                               in
                                                            [uu____16045]  in
                                                          uu____16025 ::
                                                            uu____16034
                                                           in
                                                        let uu____16078 =
                                                          let uu____16089 =
                                                            let uu____16100 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            let uu____16109 =
                                                              let uu____16120
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  head1
                                                                 in
                                                              let uu____16129
                                                                =
                                                                let uu____16140
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.tun
                                                                   in
                                                                let uu____16149
                                                                  =
                                                                  let uu____16160
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    body2  in
                                                                  [uu____16160]
                                                                   in
                                                                uu____16140
                                                                  ::
                                                                  uu____16149
                                                                 in
                                                              uu____16120 ::
                                                                uu____16129
                                                               in
                                                            uu____16100 ::
                                                              uu____16109
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____16089
                                                           in
                                                        FStar_List.append
                                                          uu____16014
                                                          uu____16078)
                                                      in
                                                   let uu____16225 =
                                                     let uu____16226 =
                                                       let uu____16240 =
                                                         let uu____16243 =
                                                           let uu____16250 =
                                                             let uu____16251
                                                               =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 head_bv
                                                                in
                                                             [uu____16251]
                                                              in
                                                           FStar_Syntax_Subst.close
                                                             uu____16250
                                                            in
                                                         let uu____16270 =
                                                           FStar_Syntax_Syntax.mk
                                                             (FStar_Syntax_Syntax.Tm_app
                                                                (bind_inst,
                                                                  args)) rng
                                                            in
                                                         FStar_All.pipe_left
                                                           uu____16243
                                                           uu____16270
                                                          in
                                                       ((false, [lb_head]),
                                                         uu____16240)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_let
                                                       uu____16226
                                                      in
                                                   FStar_Syntax_Syntax.mk
                                                     uu____16225 rng
                                                    in
                                                 (FStar_TypeChecker_Cfg.log
                                                    cfg
                                                    (fun uu____16302  ->
                                                       let uu____16303 =
                                                         FStar_Syntax_Print.term_to_string
                                                           top0
                                                          in
                                                       let uu____16305 =
                                                         FStar_Syntax_Print.term_to_string
                                                           reified
                                                          in
                                                       FStar_Util.print2
                                                         "Reified (1) <%s> to %s\n"
                                                         uu____16303
                                                         uu____16305);
                                                  (let uu____16308 =
                                                     FStar_List.tl stack1  in
                                                   norm cfg env1 uu____16308
                                                     reified)))))))
                  | FStar_Syntax_Syntax.Tm_app (head,args) ->
                      ((let uu____16336 = FStar_Options.defensive ()  in
                        if uu____16336
                        then
                          let is_arg_impure uu____16351 =
                            match uu____16351 with
                            | (e,q) ->
                                let uu____16365 =
                                  let uu____16366 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16366.FStar_Syntax_Syntax.n  in
                                (match uu____16365 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____16382 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____16382
                                 | uu____16384 -> false)
                             in
                          let uu____16386 =
                            let uu____16388 =
                              let uu____16399 =
                                FStar_Syntax_Syntax.as_arg head  in
                              uu____16399 :: args  in
                            FStar_Util.for_some is_arg_impure uu____16388  in
                          (if uu____16386
                           then
                             let uu____16425 =
                               let uu____16431 =
                                 let uu____16433 =
                                   FStar_Syntax_Print.term_to_string top2  in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____16433
                                  in
                               (FStar_Errors.Warning_Defensive, uu____16431)
                                in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu____16425
                           else ())
                        else ());
                       (let fallback1 uu____16446 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16450  ->
                               let uu____16451 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____16451 "");
                          (let uu____16455 = FStar_List.tl stack1  in
                           let uu____16456 = FStar_Syntax_Util.mk_reify top2
                              in
                           norm cfg env1 uu____16455 uu____16456)
                           in
                        let fallback2 uu____16462 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16466  ->
                               let uu____16467 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____16467 "");
                          (let uu____16471 = FStar_List.tl stack1  in
                           let uu____16472 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env1 uu____16471 uu____16472)
                           in
                        let uu____16477 =
                          let uu____16478 = FStar_Syntax_Util.un_uinst head
                             in
                          uu____16478.FStar_Syntax_Syntax.n  in
                        match uu____16477 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____16484 =
                              let uu____16486 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____16486  in
                            if uu____16484
                            then fallback1 ()
                            else
                              (let uu____16491 =
                                 let uu____16493 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____16493  in
                               if uu____16491
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____16508 =
                                      FStar_Syntax_Util.mk_reify head  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____16508
                                      args t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____16509 = FStar_List.tl stack1  in
                                  norm cfg env1 uu____16509 t1))
                        | uu____16510 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____16512) ->
                      do_reify_monadic fallback cfg env1 stack1 e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____16536 = closure_as_term cfg env1 t'  in
                        reify_lift cfg e msrc mtgt uu____16536  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____16540  ->
                            let uu____16541 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____16541);
                       (let uu____16544 = FStar_List.tl stack1  in
                        norm cfg env1 uu____16544 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches1) ->
                      let branches2 =
                        FStar_All.pipe_right branches1
                          (FStar_List.map
                             (fun uu____16665  ->
                                match uu____16665 with
                                | (pat,wopt,tm) ->
                                    let uu____16713 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16713)))
                         in
                      let tm =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_match (e, branches2))
                          top2.FStar_Syntax_Syntax.pos
                         in
                      let uu____16745 = FStar_List.tl stack1  in
                      norm cfg env1 uu____16745 tm
                  | uu____16746 -> fallback ()))

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
              (fun uu____16760  ->
                 let uu____16761 = FStar_Ident.string_of_lid msrc  in
                 let uu____16763 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16765 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16761
                   uu____16763 uu____16765);
            (let uu____16768 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16771 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env1)
                     in
                  Prims.op_Negation uu____16771)
                in
             if uu____16768
             then
               let ed =
                 let uu____16776 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env1 uu____16776  in
               let uu____16777 =
                 let uu____16786 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 FStar_All.pipe_right uu____16786 FStar_Util.must  in
               match uu____16777 with
               | (uu____16833,repr) ->
                   let uu____16843 =
                     let uu____16852 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr
                        in
                     FStar_All.pipe_right uu____16852 FStar_Util.must  in
                   (match uu____16843 with
                    | (uu____16899,return_repr) ->
                        let return_inst =
                          let uu____16912 =
                            let uu____16913 =
                              FStar_Syntax_Subst.compress return_repr  in
                            uu____16913.FStar_Syntax_Syntax.n  in
                          match uu____16912 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm,uu____16919::[]) ->
                              let uu____16924 =
                                let uu____16925 =
                                  let uu____16932 =
                                    let uu____16933 =
                                      env1.FStar_TypeChecker_Env.universe_of
                                        env1 t
                                       in
                                    [uu____16933]  in
                                  (return_tm, uu____16932)  in
                                FStar_Syntax_Syntax.Tm_uinst uu____16925  in
                              FStar_Syntax_Syntax.mk uu____16924
                                e.FStar_Syntax_Syntax.pos
                          | uu____16936 ->
                              failwith "NIY : Reification of indexed effects"
                           in
                        let uu____16940 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t
                             in
                          let lb =
                            let uu____16951 =
                              let uu____16954 =
                                let uu____16965 =
                                  FStar_Syntax_Syntax.as_arg t  in
                                [uu____16965]  in
                              FStar_Syntax_Util.mk_app repr uu____16954  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Util.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu____16951;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            }  in
                          let uu____16992 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (lb, bv, uu____16992)  in
                        (match uu____16940 with
                         | (lb_e,e_bv,e1) ->
                             let uu____17004 =
                               let uu____17005 =
                                 let uu____17019 =
                                   let uu____17022 =
                                     let uu____17029 =
                                       let uu____17030 =
                                         FStar_Syntax_Syntax.mk_binder e_bv
                                          in
                                       [uu____17030]  in
                                     FStar_Syntax_Subst.close uu____17029  in
                                   let uu____17049 =
                                     let uu____17050 =
                                       let uu____17051 =
                                         let uu____17068 =
                                           let uu____17079 =
                                             FStar_Syntax_Syntax.as_arg t  in
                                           let uu____17088 =
                                             let uu____17099 =
                                               FStar_Syntax_Syntax.as_arg e1
                                                in
                                             [uu____17099]  in
                                           uu____17079 :: uu____17088  in
                                         (return_inst, uu____17068)  in
                                       FStar_Syntax_Syntax.Tm_app uu____17051
                                        in
                                     FStar_Syntax_Syntax.mk uu____17050
                                       e1.FStar_Syntax_Syntax.pos
                                      in
                                   FStar_All.pipe_left uu____17022
                                     uu____17049
                                    in
                                 ((false, [lb_e]), uu____17019)  in
                               FStar_Syntax_Syntax.Tm_let uu____17005  in
                             FStar_Syntax_Syntax.mk uu____17004
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu____17161 =
                  FStar_TypeChecker_Env.monad_leq env1 msrc mtgt  in
                match uu____17161 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17164 =
                      let uu____17166 = FStar_Ident.string_of_lid msrc  in
                      let uu____17168 = FStar_Ident.string_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17166 uu____17168
                       in
                    failwith uu____17164
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17171;
                      FStar_TypeChecker_Env.mtarget = uu____17172;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17173;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17193 =
                      let uu____17195 = FStar_Ident.string_of_lid msrc  in
                      let uu____17197 = FStar_Ident.string_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17195 uu____17197
                       in
                    failwith uu____17193
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17200;
                      FStar_TypeChecker_Env.mtarget = uu____17201;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17202;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____17233 =
                        FStar_TypeChecker_Env.is_reifiable_effect env1 msrc
                         in
                      if uu____17233
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____17238 =
                           let uu____17239 =
                             let uu____17258 =
                               let uu____17267 =
                                 FStar_Syntax_Syntax.null_binder
                                   FStar_Syntax_Syntax.t_unit
                                  in
                               [uu____17267]  in
                             (uu____17258, e,
                               (FStar_Pervasives_Native.Some
                                  {
                                    FStar_Syntax_Syntax.residual_effect =
                                      msrc;
                                    FStar_Syntax_Syntax.residual_typ =
                                      (FStar_Pervasives_Native.Some t);
                                    FStar_Syntax_Syntax.residual_flags = []
                                  }))
                              in
                           FStar_Syntax_Syntax.Tm_abs uu____17239  in
                         FStar_Syntax_Syntax.mk uu____17238
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____17300 =
                      env1.FStar_TypeChecker_Env.universe_of env1 t  in
                    lift uu____17300 t e1))

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
                (fun uu____17370  ->
                   match uu____17370 with
                   | (a,imp) ->
                       let uu____17389 = norm cfg env1 [] a  in
                       (uu____17389, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env1  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17399  ->
             let uu____17400 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17402 =
               FStar_Util.string_of_int (FStar_List.length env1)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17400 uu____17402);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env1 [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17428 = norm_universe cfg env1 u  in
                   FStar_All.pipe_left
                     (fun uu____17431  ->
                        FStar_Pervasives_Native.Some uu____17431) uu____17428
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2125_17432 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2125_17432.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2125_17432.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env1 [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17454 = norm_universe cfg env1 u  in
                   FStar_All.pipe_left
                     (fun uu____17457  ->
                        FStar_Pervasives_Native.Some uu____17457) uu____17454
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2136_17458 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2136_17458.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2136_17458.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17503  ->
                      match uu____17503 with
                      | (a,i) ->
                          let uu____17523 = norm cfg env1 [] a  in
                          (uu____17523, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17545  ->
                       match uu___14_17545 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17549 = norm cfg env1 [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17549
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env1)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env1 [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2153_17557 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2155_17560 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2155_17560.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2153_17557.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2153_17557.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env1  ->
      fun b  ->
        let uu____17564 = b  in
        match uu____17564 with
        | (x,imp) ->
            let x1 =
              let uu___2163_17572 = x  in
              let uu____17573 = norm cfg env1 [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2163_17572.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2163_17572.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17573
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                  (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
                  let uu____17584 =
                    let uu____17585 =
                      let uu____17586 = closure_as_term cfg env1 t  in
                      FStar_Syntax_Syntax.Arg_qualifier_meta_tac uu____17586
                       in
                    FStar_Syntax_Syntax.Meta uu____17585  in
                  FStar_Pervasives_Native.Some uu____17584
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                  (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
                  let uu____17592 =
                    let uu____17593 =
                      let uu____17594 = closure_as_term cfg env1 t  in
                      FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____17594
                       in
                    FStar_Syntax_Syntax.Meta uu____17593  in
                  FStar_Pervasives_Native.Some uu____17592
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env1  ->
      fun bs  ->
        let uu____17605 =
          FStar_List.fold_left
            (fun uu____17639  ->
               fun b  ->
                 match uu____17639 with
                 | (nbs',env2) ->
                     let b1 = norm_binder cfg env2 b  in
                     ((b1 :: nbs'), (dummy :: env2))) ([], env1) bs
           in
        match uu____17605 with | (nbs,uu____17719) -> FStar_List.rev nbs

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
            let uu____17751 =
              let uu___2193_17752 = rc  in
              let uu____17753 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env1 [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2193_17752.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17753;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2193_17752.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17751
        | uu____17771 -> lopt

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
            (let uu____17781 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17783 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17781 uu____17783)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_17795  ->
      match uu___15_17795 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17808 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17808 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17812 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____17812)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun tm  ->
          let tm1 =
            let uu____17820 = norm_cb cfg  in
            reduce_primops uu____17820 cfg env1 tm  in
          let uu____17825 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17825
          then tm1
          else
            (let w t =
               let uu___2222_17844 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2222_17844.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2222_17844.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17856 =
                 let uu____17857 = FStar_Syntax_Util.unmeta t  in
                 uu____17857.FStar_Syntax_Syntax.n  in
               match uu____17856 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17869 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17933)::args1,(bv,uu____17936)::bs1) ->
                   let uu____17990 =
                     let uu____17991 = FStar_Syntax_Subst.compress t  in
                     uu____17991.FStar_Syntax_Syntax.n  in
                   (match uu____17990 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17996 -> false)
               | ([],[]) -> true
               | (uu____18027,uu____18028) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18079 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18081 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18079
                    uu____18081)
               else ();
               (let uu____18086 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18086 with
                | (hd,args) ->
                    let uu____18125 =
                      let uu____18126 = FStar_Syntax_Subst.compress hd  in
                      uu____18126.FStar_Syntax_Syntax.n  in
                    (match uu____18125 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____18134 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18136 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18138 =
                               FStar_Syntax_Print.term_to_string hd  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18134 uu____18136 uu____18138)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18143 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18161 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18163 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18161
                    uu____18163)
               else ();
               (let uu____18168 = FStar_Syntax_Util.is_squash t  in
                match uu____18168 with
                | FStar_Pervasives_Native.Some (uu____18179,t') ->
                    is_applied bs t'
                | uu____18191 ->
                    let uu____18200 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18200 with
                     | FStar_Pervasives_Native.Some (uu____18211,t') ->
                         is_applied bs t'
                     | uu____18223 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18247 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18247 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18254)::(q,uu____18256)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18299 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18301 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18299 uu____18301)
                    else ();
                    (let uu____18306 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18306 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18311 =
                           let uu____18312 = FStar_Syntax_Subst.compress p
                              in
                           uu____18312.FStar_Syntax_Syntax.n  in
                         (match uu____18311 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18323 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18323))
                          | uu____18326 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18329)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18354 =
                           let uu____18355 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18355.FStar_Syntax_Syntax.n  in
                         (match uu____18354 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18366 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18366))
                          | uu____18369 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18373 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18373 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18378 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18378 with
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
                                     let uu____18392 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18392))
                               | uu____18395 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18400)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18425 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18425 with
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
                                     let uu____18439 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18439))
                               | uu____18442 -> FStar_Pervasives_Native.None)
                          | uu____18445 -> FStar_Pervasives_Native.None)
                     | uu____18448 -> FStar_Pervasives_Native.None))
               | uu____18451 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18464 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18464 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18470)::[],uu____18471,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18491 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18493 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18491
                         uu____18493)
                    else ();
                    is_quantified_const bv phi')
               | uu____18498 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18513 =
                 let uu____18514 = FStar_Syntax_Subst.compress phi  in
                 uu____18514.FStar_Syntax_Syntax.n  in
               match uu____18513 with
               | FStar_Syntax_Syntax.Tm_match (uu____18520,br::brs) ->
                   let uu____18587 = br  in
                   (match uu____18587 with
                    | (uu____18605,uu____18606,e) ->
                        let r =
                          let uu____18628 = simp_t e  in
                          match uu____18628 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18640 =
                                FStar_List.for_all
                                  (fun uu____18659  ->
                                     match uu____18659 with
                                     | (uu____18673,uu____18674,e') ->
                                         let uu____18688 = simp_t e'  in
                                         uu____18688 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18640
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18704 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18714 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18714
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18750 =
                 match uu____18750 with
                 | (t1,q) ->
                     let uu____18771 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18771 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18803 -> (t1, q))
                  in
               let uu____18816 = FStar_Syntax_Util.head_and_args t  in
               match uu____18816 with
               | (head,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head args1
                     t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18894 =
                 let uu____18895 = FStar_Syntax_Util.unmeta ty  in
                 uu____18895.FStar_Syntax_Syntax.n  in
               match uu____18894 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18900) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18905,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18929 -> false  in
             let simplify arg =
               let uu____18962 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18962, arg)  in
             let uu____18977 = is_forall_const tm1  in
             match uu____18977 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____18983 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18985 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18983
                       uu____18985)
                  else ();
                  (let uu____18990 = norm cfg env1 [] tm'  in
                   maybe_simplify_aux cfg env1 stack1 uu____18990))
             | FStar_Pervasives_Native.None  ->
                 let uu____18991 =
                   let uu____18992 = FStar_Syntax_Subst.compress tm1  in
                   uu____18992.FStar_Syntax_Syntax.n  in
                 (match uu____18991 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18996;
                              FStar_Syntax_Syntax.vars = uu____18997;_},uu____18998);
                         FStar_Syntax_Syntax.pos = uu____18999;
                         FStar_Syntax_Syntax.vars = uu____19000;_},args)
                      ->
                      let uu____19030 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19030
                      then
                        let uu____19033 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        (match uu____19033 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19091)::
                             (uu____19092,(arg,uu____19094))::[] ->
                             maybe_auto_squash arg
                         | (uu____19167,(arg,uu____19169))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19170)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19243)::uu____19244::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19314::(FStar_Pervasives_Native.Some (false
                                         ),uu____19315)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19385 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19403 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19403
                         then
                           let uu____19406 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify)
                              in
                           match uu____19406 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19464)::uu____19465::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19535::(FStar_Pervasives_Native.Some (true
                                           ),uu____19536)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19606)::(uu____19607,(arg,uu____19609))::[]
                               -> maybe_auto_squash arg
                           | (uu____19682,(arg,uu____19684))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19685)::[]
                               -> maybe_auto_squash arg
                           | uu____19758 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19776 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19776
                            then
                              let uu____19779 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify)
                                 in
                              match uu____19779 with
                              | uu____19837::(FStar_Pervasives_Native.Some
                                              (true ),uu____19838)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19908)::uu____19909::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19979)::(uu____19980,(arg,uu____19982))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20055,(p,uu____20057))::(uu____20058,
                                                                (q,uu____20060))::[]
                                  ->
                                  let uu____20132 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20132
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20137 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20155 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20155
                               then
                                 let uu____20158 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify)
                                    in
                                 match uu____20158 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20216)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20217)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20291)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20292)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20366)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20367)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20441)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20442)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20516,(arg,uu____20518))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20519)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20592)::(uu____20593,(arg,uu____20595))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20668,(arg,uu____20670))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20671)::[]
                                     ->
                                     let uu____20744 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20744
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20745)::(uu____20746,(arg,uu____20748))::[]
                                     ->
                                     let uu____20821 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20821
                                 | (uu____20822,(p,uu____20824))::(uu____20825,
                                                                   (q,uu____20827))::[]
                                     ->
                                     let uu____20899 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20899
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20904 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20922 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20922
                                  then
                                    let uu____20925 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify)
                                       in
                                    match uu____20925 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20983)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21027)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21071 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21089 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21089
                                     then
                                       match args with
                                       | (t,uu____21093)::[] ->
                                           let uu____21118 =
                                             let uu____21119 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21119.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21118 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21122::[],body,uu____21124)
                                                ->
                                                let uu____21159 = simp_t body
                                                   in
                                                (match uu____21159 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21165 -> tm1)
                                            | uu____21169 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21171))::(t,uu____21173)::[]
                                           ->
                                           let uu____21213 =
                                             let uu____21214 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21214.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21213 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21217::[],body,uu____21219)
                                                ->
                                                let uu____21254 = simp_t body
                                                   in
                                                (match uu____21254 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21262 -> tm1)
                                            | uu____21266 -> tm1)
                                       | uu____21267 -> tm1
                                     else
                                       (let uu____21280 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21280
                                        then
                                          match args with
                                          | (t,uu____21284)::[] ->
                                              let uu____21309 =
                                                let uu____21310 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21310.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21309 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21313::[],body,uu____21315)
                                                   ->
                                                   let uu____21350 =
                                                     simp_t body  in
                                                   (match uu____21350 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21356 -> tm1)
                                               | uu____21360 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21362))::(t,uu____21364)::[]
                                              ->
                                              let uu____21404 =
                                                let uu____21405 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21405.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21404 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21408::[],body,uu____21410)
                                                   ->
                                                   let uu____21445 =
                                                     simp_t body  in
                                                   (match uu____21445 with
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
                                                    | uu____21453 -> tm1)
                                               | uu____21457 -> tm1)
                                          | uu____21458 -> tm1
                                        else
                                          (let uu____21471 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21471
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21474;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21475;_},uu____21476)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21502;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21503;_},uu____21504)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21530 -> tm1
                                           else
                                             (let uu____21543 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____21543
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____21557 =
                                                    let uu____21558 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____21558.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____21557 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21569 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21583 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____21583
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____21622 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____21622
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21628 =
                                                         let uu____21629 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____21629.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____21628 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21632 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____21640 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____21640
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21649
                                                                  =
                                                                  let uu____21650
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____21650.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____21649
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,uu____21656)
                                                                    -> hd
                                                                | uu____21681
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____21685
                                                                =
                                                                let uu____21696
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____21696]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21685)
                                                       | uu____21729 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21734 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____21734 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21754 ->
                                                     let uu____21763 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____21763 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21769;
                         FStar_Syntax_Syntax.vars = uu____21770;_},args)
                      ->
                      let uu____21796 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21796
                      then
                        let uu____21799 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        (match uu____21799 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21857)::
                             (uu____21858,(arg,uu____21860))::[] ->
                             maybe_auto_squash arg
                         | (uu____21933,(arg,uu____21935))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21936)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22009)::uu____22010::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22080::(FStar_Pervasives_Native.Some (false
                                         ),uu____22081)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22151 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22169 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22169
                         then
                           let uu____22172 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify)
                              in
                           match uu____22172 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22230)::uu____22231::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22301::(FStar_Pervasives_Native.Some (true
                                           ),uu____22302)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22372)::(uu____22373,(arg,uu____22375))::[]
                               -> maybe_auto_squash arg
                           | (uu____22448,(arg,uu____22450))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22451)::[]
                               -> maybe_auto_squash arg
                           | uu____22524 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22542 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22542
                            then
                              let uu____22545 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify)
                                 in
                              match uu____22545 with
                              | uu____22603::(FStar_Pervasives_Native.Some
                                              (true ),uu____22604)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22674)::uu____22675::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22745)::(uu____22746,(arg,uu____22748))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22821,(p,uu____22823))::(uu____22824,
                                                                (q,uu____22826))::[]
                                  ->
                                  let uu____22898 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22898
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22903 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22921 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22921
                               then
                                 let uu____22924 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify)
                                    in
                                 match uu____22924 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22982)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22983)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23057)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23058)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23132)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23133)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23207)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23208)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23282,(arg,uu____23284))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23285)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23358)::(uu____23359,(arg,uu____23361))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23434,(arg,uu____23436))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23437)::[]
                                     ->
                                     let uu____23510 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23510
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23511)::(uu____23512,(arg,uu____23514))::[]
                                     ->
                                     let uu____23587 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23587
                                 | (uu____23588,(p,uu____23590))::(uu____23591,
                                                                   (q,uu____23593))::[]
                                     ->
                                     let uu____23665 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23665
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23670 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23688 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23688
                                  then
                                    let uu____23691 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify)
                                       in
                                    match uu____23691 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23749)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23793)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23837 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23855 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23855
                                     then
                                       match args with
                                       | (t,uu____23859)::[] ->
                                           let uu____23884 =
                                             let uu____23885 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23885.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23884 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23888::[],body,uu____23890)
                                                ->
                                                let uu____23925 = simp_t body
                                                   in
                                                (match uu____23925 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23931 -> tm1)
                                            | uu____23935 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23937))::(t,uu____23939)::[]
                                           ->
                                           let uu____23979 =
                                             let uu____23980 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23980.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23979 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23983::[],body,uu____23985)
                                                ->
                                                let uu____24020 = simp_t body
                                                   in
                                                (match uu____24020 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24028 -> tm1)
                                            | uu____24032 -> tm1)
                                       | uu____24033 -> tm1
                                     else
                                       (let uu____24046 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24046
                                        then
                                          match args with
                                          | (t,uu____24050)::[] ->
                                              let uu____24075 =
                                                let uu____24076 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24076.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24075 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24079::[],body,uu____24081)
                                                   ->
                                                   let uu____24116 =
                                                     simp_t body  in
                                                   (match uu____24116 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24122 -> tm1)
                                               | uu____24126 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24128))::(t,uu____24130)::[]
                                              ->
                                              let uu____24170 =
                                                let uu____24171 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24171.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24170 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24174::[],body,uu____24176)
                                                   ->
                                                   let uu____24211 =
                                                     simp_t body  in
                                                   (match uu____24211 with
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
                                                    | uu____24219 -> tm1)
                                               | uu____24223 -> tm1)
                                          | uu____24224 -> tm1
                                        else
                                          (let uu____24237 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24237
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24240;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24241;_},uu____24242)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24268;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24269;_},uu____24270)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24296 -> tm1
                                           else
                                             (let uu____24309 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____24309
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____24323 =
                                                    let uu____24324 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____24324.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____24323 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____24335 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24349 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____24349
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____24384 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____24384
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24390 =
                                                         let uu____24391 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____24391.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____24390 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24394 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24402 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24402
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24411
                                                                  =
                                                                  let uu____24412
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24412.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24411
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,uu____24418)
                                                                    -> hd
                                                                | uu____24443
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____24447
                                                                =
                                                                let uu____24458
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____24458]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24447)
                                                       | uu____24491 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24496 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____24496 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24516 ->
                                                     let uu____24525 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____24525 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24536 = simp_t t  in
                      (match uu____24536 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24545 ->
                      let uu____24568 = is_const_match tm1  in
                      (match uu____24568 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24577 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____24587  ->
               (let uu____24589 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24591 = FStar_Syntax_Print.term_to_string t  in
                let uu____24593 =
                  FStar_Util.string_of_int (FStar_List.length env1)  in
                let uu____24601 =
                  let uu____24603 =
                    let uu____24606 = firstn (Prims.of_int (4)) stack1  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24606
                     in
                  stack_to_string uu____24603  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24589 uu____24591 uu____24593 uu____24601);
               (let uu____24631 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24631
                then
                  let uu____24635 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24635 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24642 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24644 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24646 =
                          let uu____24648 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24648
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24642
                          uu____24644 uu____24646);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____24670 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack1 with
                | (Arg uu____24678)::uu____24679 -> true
                | uu____24689 -> false)
              in
           if uu____24670
           then
             let uu____24692 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____24692 (norm cfg env1 stack1)
           else
             (let t1 = maybe_simplify cfg env1 stack1 t  in
              match stack1 with
              | [] -> t1
              | (Debug (tm,time_then))::stack2 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____24706 =
                        let uu____24708 =
                          let uu____24710 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____24710  in
                        FStar_Util.string_of_int uu____24708  in
                      let uu____24717 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____24719 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                      let uu____24721 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____24706 uu____24717 uu____24719 uu____24721)
                   else ();
                   rebuild cfg env1 stack2 t1)
              | (Cfg cfg1)::stack2 -> rebuild cfg1 env1 stack2 t1
              | (Meta (uu____24730,m,r))::stack2 ->
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_meta (t1, m)) r
                     in
                  rebuild cfg env1 stack2 t2
              | (MemoLazy r)::stack2 ->
                  (set_memo cfg r (env1, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24759  ->
                        let uu____24760 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24760);
                   rebuild cfg env1 stack2 t1)
              | (Let (env',bs,lb,r))::stack2 ->
                  let body = FStar_Syntax_Subst.close bs t1  in
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let ((false, [lb]), body)) r
                     in
                  rebuild cfg env' stack2 t2
              | (Abs (env',bs,env'',lopt,r))::stack2 ->
                  let bs1 = norm_binders cfg env' bs  in
                  let lopt1 = norm_lcomp_opt cfg env'' lopt  in
                  let uu____24803 =
                    let uu___2851_24804 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2851_24804.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2851_24804.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env1 stack2 uu____24803
              | (Arg (Univ uu____24807,uu____24808,uu____24809))::uu____24810
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____24814,uu____24815))::uu____24816 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env1 stack2 t2
              | (Arg
                  (Clos (env_arg,tm,uu____24832,uu____24833),aq,r))::stack2
                  when
                  let uu____24885 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24885 ->
                  let t2 =
                    let uu____24887 =
                      let uu____24888 = closure_as_term cfg env_arg tm  in
                      (uu____24888, aq)  in
                    FStar_Syntax_Syntax.extend_app t1 uu____24887 r  in
                  rebuild cfg env1 stack2 t2
              | (Arg (Clos (env_arg,tm,m,uu____24898),aq,r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24953  ->
                        let uu____24954 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____24954);
                   if
                     Prims.op_Negation
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                   then
                     (let uu____24958 =
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                          &&
                          (let uu____24961 = is_partial_primop_app cfg t1  in
                           Prims.op_Negation uu____24961)
                         in
                      if uu____24958
                      then
                        let arg = closure_as_term cfg env_arg tm  in
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (arg, aq) r  in
                        rebuild cfg env_arg stack2 t2
                      else
                        (let stack3 = (App (env1, t1, aq, r)) :: stack2  in
                         norm cfg env_arg stack3 tm))
                   else
                     (let uu____24977 = FStar_ST.op_Bang m  in
                      match uu____24977 with
                      | FStar_Pervasives_Native.None  ->
                          let uu____25051 =
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                              &&
                              (let uu____25054 = is_partial_primop_app cfg t1
                                  in
                               Prims.op_Negation uu____25054)
                             in
                          if uu____25051
                          then
                            let arg = closure_as_term cfg env_arg tm  in
                            let t2 =
                              FStar_Syntax_Syntax.extend_app t1 (arg, aq) r
                               in
                            rebuild cfg env_arg stack2 t2
                          else
                            (let stack3 = (MemoLazy m) ::
                               (App (env1, t1, aq, r)) :: stack2  in
                             norm cfg env_arg stack3 tm)
                      | FStar_Pervasives_Native.Some (uu____25068,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq) r  in
                          rebuild cfg env_arg stack2 t2))
              | (App (env2,head,aq,r))::stack' when should_reify cfg stack1
                  ->
                  let t0 = t1  in
                  let fallback msg uu____25122 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____25127  ->
                         let uu____25128 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____25128);
                    (let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r
                        in
                     rebuild cfg env2 stack' t2)
                     in
                  let uu____25136 =
                    let uu____25137 = FStar_Syntax_Subst.compress t1  in
                    uu____25137.FStar_Syntax_Syntax.n  in
                  (match uu____25136 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env2 stack1 t2
                         m ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____25165 = closure_as_term cfg env2 ty  in
                         reify_lift cfg t2 msrc mtgt uu____25165  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____25169  ->
                             let uu____25170 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____25170);
                        (let uu____25173 = FStar_List.tl stack1  in
                         norm cfg env2 uu____25173 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____25174);
                          FStar_Syntax_Syntax.pos = uu____25175;
                          FStar_Syntax_Syntax.vars = uu____25176;_},(e,uu____25178)::[])
                       -> norm cfg env2 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____25217 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____25234 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____25234 with
                        | (hd,args) ->
                            let uu____25277 =
                              let uu____25278 = FStar_Syntax_Util.un_uinst hd
                                 in
                              uu____25278.FStar_Syntax_Syntax.n  in
                            (match uu____25277 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____25282 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____25282 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____25285;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____25286;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____25287;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____25289;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____25290;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____25291;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____25292;_}
                                      when (FStar_List.length args) = n ->
                                      norm cfg env2 stack' t1
                                  | uu____25328 -> fallback " (3)" ())
                             | uu____25332 -> fallback " (4)" ()))
                   | uu____25334 -> fallback " (2)" ())
              | (App (env2,head,aq,r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r  in
                  rebuild cfg env2 stack2 t2
              | (CBVApp (env',head,aq,r))::stack2 ->
                  let uu____25355 =
                    let uu____25356 =
                      let uu____25357 =
                        let uu____25364 =
                          let uu____25365 =
                            let uu____25397 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env1, t1, uu____25397, false)  in
                          Clos uu____25365  in
                        (uu____25364, aq, (t1.FStar_Syntax_Syntax.pos))  in
                      Arg uu____25357  in
                    uu____25356 :: stack2  in
                  norm cfg env' uu____25355 head
              | (Match (env',branches1,cfg1,r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____25472  ->
                        let uu____25473 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____25473);
                   (let scrutinee_env = env1  in
                    let env2 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____25484 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25489  ->
                           let uu____25490 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____25492 =
                             let uu____25494 =
                               FStar_All.pipe_right branches1
                                 (FStar_List.map
                                    (fun uu____25524  ->
                                       match uu____25524 with
                                       | (p,uu____25535,uu____25536) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____25494
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____25490 uu____25492);
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
                                   (fun uu___16_25561  ->
                                      match uu___16_25561 with
                                      | FStar_TypeChecker_Env.InliningDelta 
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                           -> true
                                      | uu____25565 -> false))
                               in
                            let steps =
                              let uu___3028_25568 =
                                cfg1.FStar_TypeChecker_Cfg.steps  in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3028_25568.FStar_TypeChecker_Cfg.for_extraction)
                              }  in
                            let uu___3031_25575 = cfg1  in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3031_25575.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3031_25575.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3031_25575.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3031_25575.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3031_25575.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3031_25575.FStar_TypeChecker_Cfg.reifying)
                            })
                          in
                       let norm_or_whnf env3 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env3 t2
                         else norm cfg_exclude_zeta env3 [] t2  in
                       let rec norm_pat env3 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____25650 ->
                             (p, env3)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____25681 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25770  ->
                                       fun uu____25771  ->
                                         match (uu____25770, uu____25771)
                                         with
                                         | ((pats1,env4),(p1,b)) ->
                                             let uu____25921 =
                                               norm_pat env4 p1  in
                                             (match uu____25921 with
                                              | (p2,env5) ->
                                                  (((p2, b) :: pats1), env5)))
                                    ([], env3))
                                in
                             (match uu____25681 with
                              | (pats1,env4) ->
                                  ((let uu___3059_26091 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3059_26091.FStar_Syntax_Syntax.p)
                                    }), env4))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3063_26112 = x  in
                               let uu____26113 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3063_26112.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3063_26112.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26113
                               }  in
                             ((let uu___3066_26127 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3066_26127.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3070_26138 = x  in
                               let uu____26139 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3070_26138.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3070_26138.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26139
                               }  in
                             ((let uu___3073_26153 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3073_26153.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3079_26169 = x  in
                               let uu____26170 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3079_26169.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3079_26169.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26170
                               }  in
                             let t3 = norm_or_whnf env3 t2  in
                             ((let uu___3083_26185 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3083_26185.FStar_Syntax_Syntax.p)
                               }), env3)
                          in
                       let branches2 =
                         match env2 with
                         | [] when whnf -> branches1
                         | uu____26229 ->
                             FStar_All.pipe_right branches1
                               (FStar_List.map
                                  (fun branch  ->
                                     let uu____26259 =
                                       FStar_Syntax_Subst.open_branch branch
                                        in
                                     match uu____26259 with
                                     | (p,wopt,e) ->
                                         let uu____26279 = norm_pat env2 p
                                            in
                                         (match uu____26279 with
                                          | (p1,env3) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____26334 =
                                                      norm_or_whnf env3 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____26334
                                                 in
                                              let e1 = norm_or_whnf env3 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____26351 =
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
                         if uu____26351
                         then
                           norm
                             (let uu___3102_26358 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3104_26361 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.zeta_full =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.zeta_full);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3104_26361.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3102_26358.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3102_26358.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3102_26358.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3102_26358.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3102_26358.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3102_26358.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3102_26358.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3102_26358.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____26365 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches2)) r
                          in
                       rebuild cfg1 env2 stack2 uu____26365)
                       in
                    let rec is_cons head =
                      let uu____26391 =
                        let uu____26392 = FStar_Syntax_Subst.compress head
                           in
                        uu____26392.FStar_Syntax_Syntax.n  in
                      match uu____26391 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____26397) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____26402 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26404;
                            FStar_Syntax_Syntax.fv_delta = uu____26405;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26407;
                            FStar_Syntax_Syntax.fv_delta = uu____26408;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____26409);_}
                          -> true
                      | uu____26417 -> false  in
                    let guard_when_clause wopt b rest =
                      match wopt with
                      | FStar_Pervasives_Native.None  -> b
                      | FStar_Pervasives_Native.Some w ->
                          let then_branch = b  in
                          let else_branch =
                            FStar_Syntax_Syntax.mk
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
                      let uu____26586 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____26586 with
                      | (head,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____26683 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26725 ->
                                    let uu____26726 =
                                      let uu____26728 = is_cons head  in
                                      Prims.op_Negation uu____26728  in
                                    FStar_Util.Inr uu____26726)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____26757 =
                                 let uu____26758 =
                                   FStar_Syntax_Util.un_uinst head  in
                                 uu____26758.FStar_Syntax_Syntax.n  in
                               (match uu____26757 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26777 ->
                                    let uu____26778 =
                                      let uu____26780 = is_cons head  in
                                      Prims.op_Negation uu____26780  in
                                    FStar_Util.Inr uu____26778))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____26871)::rest_a,(p1,uu____26874)::rest_p)
                          ->
                          let uu____26933 = matches_pat t2 p1  in
                          (match uu____26933 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____26986 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____27109 = matches_pat scrutinee1 p1  in
                          (match uu____27109 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____27155  ->
                                     let uu____27156 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____27158 =
                                       let uu____27160 =
                                         FStar_List.map
                                           (fun uu____27172  ->
                                              match uu____27172 with
                                              | (uu____27178,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____27160
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____27156 uu____27158);
                                (let env0 = env2  in
                                 let env3 =
                                   FStar_List.fold_left
                                     (fun env3  ->
                                        fun uu____27214  ->
                                          match uu____27214 with
                                          | (bv,t2) ->
                                              let uu____27237 =
                                                let uu____27244 =
                                                  let uu____27247 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____27247
                                                   in
                                                let uu____27248 =
                                                  let uu____27249 =
                                                    let uu____27281 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____27281,
                                                      false)
                                                     in
                                                  Clos uu____27249  in
                                                (uu____27244, uu____27248)
                                                 in
                                              uu____27237 :: env3) env2 s
                                    in
                                 let uu____27374 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env3 stack2 uu____27374)))
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
            (fun uu____27407  ->
               let uu____27408 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____27408);
          (let uu____27411 = is_nbe_request s  in
           if uu____27411
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27417  ->
                   let uu____27418 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27418);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27424  ->
                   let uu____27425 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27425);
              (let uu____27428 =
                 FStar_Util.record_time (fun uu____27435  -> nbe_eval c s t)
                  in
               match uu____27428 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27444  ->
                         let uu____27445 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27447 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27445 uu____27447);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27455  ->
                   let uu____27456 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27456);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27462  ->
                   let uu____27463 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27463);
              (let uu____27466 =
                 FStar_Util.record_time (fun uu____27473  -> norm c [] [] t)
                  in
               match uu____27466 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27488  ->
                         let uu____27489 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27491 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27489 uu____27491);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27510 =
          let uu____27514 =
            let uu____27516 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____27516  in
          FStar_Pervasives_Native.Some uu____27514  in
        FStar_Profiling.profile
          (fun uu____27519  -> normalize_with_primitive_steps [] s e t)
          uu____27510 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____27541  ->
             let uu____27542 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27542);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27548  ->
             let uu____27549 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27549);
        (let uu____27552 =
           FStar_Util.record_time (fun uu____27559  -> norm_comp cfg [] c)
            in
         match uu____27552 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27574  ->
                   let uu____27575 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____27577 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27575
                     uu____27577);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env1  ->
    fun u  ->
      let uu____27591 = FStar_TypeChecker_Cfg.config [] env1  in
      norm_universe uu____27591 [] u
  
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
      let uu____27613 = normalize steps env1 t  in
      FStar_TypeChecker_Env.non_informative env1 uu____27613
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env1  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27625 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env1 t ->
          let uu___3272_27644 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3272_27644.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3272_27644.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env1
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27651 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env1 ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27651
          then
            let ct1 =
              let uu____27655 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27655 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____27662 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27662
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3282_27669 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3282_27669.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3282_27669.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3282_27669.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env1 c
                     in
                  let uu___3286_27671 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3286_27671.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3286_27671.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3286_27671.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3286_27671.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3289_27672 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3289_27672.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3289_27672.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27675 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env1  ->
    fun lc  ->
      let uu____27687 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env1 lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____27687
      then
        let uu____27690 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____27690 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3297_27694 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env1)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3297_27694.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3297_27694.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3297_27694.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env1  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3304_27713  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                   t) ()
        with
        | uu___3303_27716 ->
            ((let uu____27718 =
                let uu____27724 =
                  let uu____27726 = FStar_Util.message_of_exn uu___3303_27716
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27726
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27724)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27718);
             t)
         in
      FStar_Syntax_Print.term_to_string' env1.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env1  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3314_27745  ->
             match () with
             | () ->
                 let uu____27746 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                    in
                 norm_comp uu____27746 [] c) ()
        with
        | uu___3313_27755 ->
            ((let uu____27757 =
                let uu____27763 =
                  let uu____27765 = FStar_Util.message_of_exn uu___3313_27755
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27765
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27763)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27757);
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
                   let uu____27814 =
                     let uu____27815 =
                       let uu____27822 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27822)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27815  in
                   FStar_Syntax_Syntax.mk uu____27814
                     t01.FStar_Syntax_Syntax.pos
               | uu____27827 -> t2)
          | uu____27828 -> t2  in
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
        let uu____27922 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27922 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27935 ->
                 let uu____27936 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27936 with
                  | (actuals,uu____27946,uu____27947) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27967 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27967 with
                         | (binders,args) ->
                             let uu____27978 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27978
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
      | uu____27993 ->
          let uu____27994 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27994 with
           | (head,args) ->
               let uu____28037 =
                 let uu____28038 = FStar_Syntax_Subst.compress head  in
                 uu____28038.FStar_Syntax_Syntax.n  in
               (match uu____28037 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____28059 =
                      let uu____28066 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____28066  in
                    (match uu____28059 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____28090 =
                              env1.FStar_TypeChecker_Env.type_of
                                (let uu___3384_28098 = env1  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3384_28098.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3384_28098.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3384_28098.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3384_28098.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3384_28098.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3384_28098.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3384_28098.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3384_28098.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3384_28098.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3384_28098.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3384_28098.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3384_28098.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3384_28098.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3384_28098.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3384_28098.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3384_28098.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3384_28098.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3384_28098.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3384_28098.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3384_28098.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3384_28098.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3384_28098.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3384_28098.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3384_28098.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3384_28098.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3384_28098.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3384_28098.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3384_28098.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3384_28098.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3384_28098.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3384_28098.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3384_28098.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3384_28098.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3384_28098.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3384_28098.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3384_28098.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3384_28098.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3384_28098.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3384_28098.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3384_28098.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3384_28098.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3384_28098.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3384_28098.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___3384_28098.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 }) t
                               in
                            match uu____28090 with
                            | (uu____28101,ty,uu____28103) ->
                                eta_expand_with_type env1 t ty))
                | uu____28104 ->
                    let uu____28105 =
                      env1.FStar_TypeChecker_Env.type_of
                        (let uu___3391_28113 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3391_28113.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3391_28113.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3391_28113.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3391_28113.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3391_28113.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3391_28113.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3391_28113.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3391_28113.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3391_28113.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3391_28113.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3391_28113.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3391_28113.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3391_28113.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3391_28113.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3391_28113.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3391_28113.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3391_28113.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3391_28113.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3391_28113.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3391_28113.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3391_28113.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3391_28113.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3391_28113.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3391_28113.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3391_28113.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3391_28113.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3391_28113.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3391_28113.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3391_28113.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3391_28113.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3391_28113.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3391_28113.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3391_28113.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3391_28113.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3391_28113.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3391_28113.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3391_28113.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3391_28113.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3391_28113.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3391_28113.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3391_28113.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3391_28113.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3391_28113.FStar_TypeChecker_Env.erasable_types_tab);
                           FStar_TypeChecker_Env.enable_defer_to_tac =
                             (uu___3391_28113.FStar_TypeChecker_Env.enable_defer_to_tac)
                         }) t
                       in
                    (match uu____28105 with
                     | (uu____28116,ty,uu____28118) ->
                         eta_expand_with_type env1 t ty)))
  
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos  in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___3403_28200 = x  in
      let uu____28201 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3403_28200.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3403_28200.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28201
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28204 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28220 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28221 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28222 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28223 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28230 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28231 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28232 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3429_28266 = rc  in
          let uu____28267 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28276 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3429_28266.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28267;
            FStar_Syntax_Syntax.residual_flags = uu____28276
          }  in
        let uu____28279 =
          let uu____28280 =
            let uu____28299 = elim_delayed_subst_binders bs  in
            let uu____28308 = elim_delayed_subst_term t2  in
            let uu____28311 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28299, uu____28308, uu____28311)  in
          FStar_Syntax_Syntax.Tm_abs uu____28280  in
        mk uu____28279
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28348 =
          let uu____28349 =
            let uu____28364 = elim_delayed_subst_binders bs  in
            let uu____28373 = elim_delayed_subst_comp c  in
            (uu____28364, uu____28373)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28349  in
        mk uu____28348
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28392 =
          let uu____28393 =
            let uu____28400 = elim_bv bv  in
            let uu____28401 = elim_delayed_subst_term phi  in
            (uu____28400, uu____28401)  in
          FStar_Syntax_Syntax.Tm_refine uu____28393  in
        mk uu____28392
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28432 =
          let uu____28433 =
            let uu____28450 = elim_delayed_subst_term t2  in
            let uu____28453 = elim_delayed_subst_args args  in
            (uu____28450, uu____28453)  in
          FStar_Syntax_Syntax.Tm_app uu____28433  in
        mk uu____28432
    | FStar_Syntax_Syntax.Tm_match (t2,branches1) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3451_28525 = p  in
              let uu____28526 =
                let uu____28527 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28527  in
              {
                FStar_Syntax_Syntax.v = uu____28526;
                FStar_Syntax_Syntax.p =
                  (uu___3451_28525.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3455_28529 = p  in
              let uu____28530 =
                let uu____28531 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28531  in
              {
                FStar_Syntax_Syntax.v = uu____28530;
                FStar_Syntax_Syntax.p =
                  (uu___3455_28529.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3461_28538 = p  in
              let uu____28539 =
                let uu____28540 =
                  let uu____28547 = elim_bv x  in
                  let uu____28548 = elim_delayed_subst_term t0  in
                  (uu____28547, uu____28548)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28540  in
              {
                FStar_Syntax_Syntax.v = uu____28539;
                FStar_Syntax_Syntax.p =
                  (uu___3461_28538.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3467_28573 = p  in
              let uu____28574 =
                let uu____28575 =
                  let uu____28589 =
                    FStar_List.map
                      (fun uu____28615  ->
                         match uu____28615 with
                         | (x,b) ->
                             let uu____28632 = elim_pat x  in
                             (uu____28632, b)) pats
                     in
                  (fv, uu____28589)  in
                FStar_Syntax_Syntax.Pat_cons uu____28575  in
              {
                FStar_Syntax_Syntax.v = uu____28574;
                FStar_Syntax_Syntax.p =
                  (uu___3467_28573.FStar_Syntax_Syntax.p)
              }
          | uu____28647 -> p  in
        let elim_branch uu____28671 =
          match uu____28671 with
          | (pat,wopt,t3) ->
              let uu____28697 = elim_pat pat  in
              let uu____28700 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28703 = elim_delayed_subst_term t3  in
              (uu____28697, uu____28700, uu____28703)
           in
        let uu____28708 =
          let uu____28709 =
            let uu____28732 = elim_delayed_subst_term t2  in
            let uu____28735 = FStar_List.map elim_branch branches1  in
            (uu____28732, uu____28735)  in
          FStar_Syntax_Syntax.Tm_match uu____28709  in
        mk uu____28708
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28866 =
          match uu____28866 with
          | (tc,topt) ->
              let uu____28901 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28911 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28911
                | FStar_Util.Inr c ->
                    let uu____28913 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28913
                 in
              let uu____28914 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28901, uu____28914)
           in
        let uu____28923 =
          let uu____28924 =
            let uu____28951 = elim_delayed_subst_term t2  in
            let uu____28954 = elim_ascription a  in
            (uu____28951, uu____28954, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28924  in
        mk uu____28923
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3497_29017 = lb  in
          let uu____29018 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____29021 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3497_29017.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3497_29017.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____29018;
            FStar_Syntax_Syntax.lbeff =
              (uu___3497_29017.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____29021;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3497_29017.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3497_29017.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____29024 =
          let uu____29025 =
            let uu____29039 =
              let uu____29047 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____29047)  in
            let uu____29059 = elim_delayed_subst_term t2  in
            (uu____29039, uu____29059)  in
          FStar_Syntax_Syntax.Tm_let uu____29025  in
        mk uu____29024
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____29104 =
          let uu____29105 =
            let uu____29112 = elim_delayed_subst_term tm  in
            (uu____29112, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____29105  in
        mk uu____29104
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29123 =
          let uu____29124 =
            let uu____29131 = elim_delayed_subst_term t2  in
            let uu____29134 = elim_delayed_subst_meta md  in
            (uu____29131, uu____29134)  in
          FStar_Syntax_Syntax.Tm_meta uu____29124  in
        mk uu____29123

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29143  ->
         match uu___17_29143 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29147 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29147
         | f -> f) flags

and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c  ->
    let mk x = FStar_Syntax_Syntax.mk x c.FStar_Syntax_Syntax.pos  in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____29170 =
          let uu____29171 =
            let uu____29180 = elim_delayed_subst_term t  in
            (uu____29180, uopt)  in
          FStar_Syntax_Syntax.Total uu____29171  in
        mk uu____29170
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29197 =
          let uu____29198 =
            let uu____29207 = elim_delayed_subst_term t  in
            (uu____29207, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29198  in
        mk uu____29197
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3530_29216 = ct  in
          let uu____29217 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29220 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29231 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3530_29216.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3530_29216.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29217;
            FStar_Syntax_Syntax.effect_args = uu____29220;
            FStar_Syntax_Syntax.flags = uu____29231
          }  in
        mk (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29234  ->
    match uu___18_29234 with
    | FStar_Syntax_Syntax.Meta_pattern (names,args) ->
        let uu____29269 =
          let uu____29290 = FStar_List.map elim_delayed_subst_term names  in
          let uu____29299 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29290, uu____29299)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29269
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____29354 =
          let uu____29361 = elim_delayed_subst_term t  in (m, uu____29361)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____29354
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____29373 =
          let uu____29382 = elim_delayed_subst_term t  in
          (m1, m2, uu____29382)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29373
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
      (fun uu____29415  ->
         match uu____29415 with
         | (t,q) ->
             let uu____29434 = elim_delayed_subst_term t  in (uu____29434, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29462  ->
         match uu____29462 with
         | (x,q) ->
             let uu____29481 =
               let uu___3556_29482 = x  in
               let uu____29483 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3556_29482.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3556_29482.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29483
               }  in
             (uu____29481, q)) bs

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
            | (uu____29591,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  c.FStar_Syntax_Syntax.pos
            | (uu____29623,FStar_Util.Inl t) ->
                let uu____29645 =
                  let uu____29646 =
                    let uu____29661 = FStar_Syntax_Syntax.mk_Total t  in
                    (binders, uu____29661)  in
                  FStar_Syntax_Syntax.Tm_arrow uu____29646  in
                FStar_Syntax_Syntax.mk uu____29645 t.FStar_Syntax_Syntax.pos
             in
          let uu____29674 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29674 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env1 t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29706 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29779 ->
                    let uu____29780 =
                      let uu____29789 =
                        let uu____29790 = FStar_Syntax_Subst.compress t4  in
                        uu____29790.FStar_Syntax_Syntax.n  in
                      (uu____29789, tc)  in
                    (match uu____29780 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29819) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29866) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29911,FStar_Util.Inl uu____29912) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29943 -> failwith "Impossible")
                 in
              (match uu____29706 with
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
          let uu____30082 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inl t)  in
          match uu____30082 with
          | (univ_names1,binders1,tc) ->
              let uu____30156 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30156)
  
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
          let uu____30210 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inr c)  in
          match uu____30210 with
          | (univ_names1,binders1,tc) ->
              let uu____30284 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30284)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env1  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____30326 = elim_uvars_aux_t env1 univ_names binders typ  in
          (match uu____30326 with
           | (univ_names1,binders1,typ1) ->
               let uu___3639_30366 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3639_30366.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3639_30366.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3639_30366.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3639_30366.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3639_30366.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3645_30381 = s  in
          let uu____30382 =
            let uu____30383 =
              let uu____30392 = FStar_List.map (elim_uvars env1) sigs  in
              (uu____30392, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____30383  in
          {
            FStar_Syntax_Syntax.sigel = uu____30382;
            FStar_Syntax_Syntax.sigrng =
              (uu___3645_30381.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3645_30381.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3645_30381.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3645_30381.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3645_30381.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____30411 = elim_uvars_aux_t env1 univ_names [] typ  in
          (match uu____30411 with
           | (univ_names1,uu____30435,typ1) ->
               let uu___3659_30457 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3659_30457.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3659_30457.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3659_30457.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3659_30457.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3659_30457.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____30464 = elim_uvars_aux_t env1 univ_names [] typ  in
          (match uu____30464 with
           | (univ_names1,uu____30488,typ1) ->
               let uu___3670_30510 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3670_30510.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3670_30510.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3670_30510.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3670_30510.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3670_30510.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30540 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30540 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____30565 =
                            let uu____30566 =
                              let uu____30567 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env1 uu____30567  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30566
                             in
                          elim_delayed_subst_term uu____30565  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3686_30570 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3686_30570.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3686_30570.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3686_30570.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3686_30570.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3689_30571 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3689_30571.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3689_30571.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3689_30571.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3689_30571.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3689_30571.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____30580 = elim_uvars_aux_t env1 us [] t  in
          (match uu____30580 with
           | (us1,uu____30604,t1) ->
               let uu___3700_30626 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3700_30626.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3700_30626.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3700_30626.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3700_30626.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3700_30626.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30628 =
            elim_uvars_aux_t env1 ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____30628 with
           | (univs,binders,uu____30647) ->
               let uu____30668 =
                 let uu____30673 = FStar_Syntax_Subst.univ_var_opening univs
                    in
                 match uu____30673 with
                 | (univs_opening,univs1) ->
                     let uu____30696 =
                       FStar_Syntax_Subst.univ_var_closing univs1  in
                     (univs_opening, uu____30696)
                  in
               (match uu____30668 with
                | (univs_opening,univs_closing) ->
                    let uu____30699 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30705 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30706 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30705, uu____30706)  in
                    (match uu____30699 with
                     | (b_opening,b_closing) ->
                         let n = FStar_List.length univs  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30732 =
                           match uu____30732 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30750 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30750 with
                                | (us1,t1) ->
                                    let uu____30761 =
                                      let uu____30770 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30775 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30770, uu____30775)  in
                                    (match uu____30761 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30798 =
                                           let uu____30807 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____30812 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____30807, uu____30812)  in
                                         (match uu____30798 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30836 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30836
                                                 in
                                              let uu____30837 =
                                                elim_uvars_aux_t env1 [] []
                                                  t2
                                                 in
                                              (match uu____30837 with
                                               | (uu____30864,uu____30865,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30888 =
                                                       let uu____30889 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30889
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30888
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30898 =
                             elim_uvars_aux_t env1 univs binders t  in
                           match uu____30898 with
                           | (uu____30917,uu____30918,t1) -> t1  in
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
                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                in
                             match a.FStar_Syntax_Syntax.action_params with
                             | [] -> body
                             | uu____30994 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____31021 =
                               let uu____31022 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____31022.FStar_Syntax_Syntax.n  in
                             match uu____31021 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____31081 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31115 =
                               let uu____31116 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31116.FStar_Syntax_Syntax.n  in
                             match uu____31115 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31139) ->
                                 let uu____31164 = destruct_action_body body
                                    in
                                 (match uu____31164 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31213 ->
                                 let uu____31214 = destruct_action_body t  in
                                 (match uu____31214 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31269 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31269 with
                           | (action_univs,t) ->
                               let uu____31278 = destruct_action_typ_templ t
                                  in
                               (match uu____31278 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3784_31325 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3784_31325.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3784_31325.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3787_31327 = ed  in
                           let uu____31328 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____31329 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____31330 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3787_31327.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3787_31327.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31328;
                             FStar_Syntax_Syntax.combinators = uu____31329;
                             FStar_Syntax_Syntax.actions = uu____31330;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3787_31327.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3790_31333 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3790_31333.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3790_31333.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3790_31333.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3790_31333.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3790_31333.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31354 =
            match uu___19_31354 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____31385 = elim_uvars_aux_t env1 us [] t  in
                (match uu____31385 with
                 | (us1,uu____31417,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3805_31448 = sub_eff  in
            let uu____31449 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____31452 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3805_31448.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3805_31448.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31449;
              FStar_Syntax_Syntax.lift = uu____31452
            }  in
          let uu___3808_31455 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3808_31455.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3808_31455.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3808_31455.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3808_31455.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3808_31455.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____31465 = elim_uvars_aux_c env1 univ_names binders comp  in
          (match uu____31465 with
           | (univ_names1,binders1,comp1) ->
               let uu___3821_31505 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3821_31505.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3821_31505.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3821_31505.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3821_31505.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3821_31505.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31508 -> s
      | FStar_Syntax_Syntax.Sig_fail uu____31509 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31522 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n,p,(us_t,t),(us_ty,ty))
          ->
          let uu____31552 = elim_uvars_aux_t env1 us_t [] t  in
          (match uu____31552 with
           | (us_t1,uu____31576,t1) ->
               let uu____31598 = elim_uvars_aux_t env1 us_ty [] ty  in
               (match uu____31598 with
                | (us_ty1,uu____31622,ty1) ->
                    let uu___3848_31644 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3848_31644.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3848_31644.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3848_31644.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3848_31644.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3848_31644.FStar_Syntax_Syntax.sigopts)
                    }))
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp (m,n,(us_t,t),(us_ty,ty))
          ->
          let uu____31675 = elim_uvars_aux_t env1 us_t [] t  in
          (match uu____31675 with
           | (us_t1,uu____31699,t1) ->
               let uu____31721 = elim_uvars_aux_t env1 us_ty [] ty  in
               (match uu____31721 with
                | (us_ty1,uu____31745,ty1) ->
                    let uu___3868_31767 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                           (m, n, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3868_31767.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3868_31767.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3868_31767.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3868_31767.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3868_31767.FStar_Syntax_Syntax.sigopts)
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
        let uu____31818 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env1 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____31818 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____31840 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____31840 with
             | (uu____31847,head_def) ->
                 let t' =
                   FStar_Syntax_Syntax.mk_Tm_app head_def args
                     t.FStar_Syntax_Syntax.pos
                    in
                 let t'1 =
                   normalize
                     [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota]
                     env1 t'
                    in
                 FStar_Pervasives_Native.Some t'1)
         in
      let uu____31851 = FStar_Syntax_Util.head_and_args t  in
      match uu____31851 with
      | (head,args) ->
          let uu____31896 =
            let uu____31897 = FStar_Syntax_Subst.compress head  in
            uu____31897.FStar_Syntax_Syntax.n  in
          (match uu____31896 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31904;
                  FStar_Syntax_Syntax.vars = uu____31905;_},us)
               -> aux fv us args
           | uu____31911 -> FStar_Pervasives_Native.None)
  
let (get_n_binders :
  FStar_TypeChecker_Env.env ->
    Prims.int ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.binder Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun env1  ->
    fun n  ->
      fun t  ->
        let rec aux retry n1 t1 =
          let uu____31974 = FStar_Syntax_Util.arrow_formals_comp t1  in
          match uu____31974 with
          | (bs,c) ->
              let len = FStar_List.length bs  in
              (match (bs, c) with
               | ([],uu____32010) when retry ->
                   let uu____32029 = unfold_whnf env1 t1  in
                   aux false n1 uu____32029
               | ([],uu____32031) when Prims.op_Negation retry -> (bs, c)
               | (bs1,c1) when len = n1 -> (bs1, c1)
               | (bs1,c1) when len > n1 ->
                   let uu____32099 = FStar_List.splitAt n1 bs1  in
                   (match uu____32099 with
                    | (bs_l,bs_r) ->
                        let uu____32166 =
                          let uu____32167 = FStar_Syntax_Util.arrow bs_r c1
                             in
                          FStar_Syntax_Syntax.mk_Total uu____32167  in
                        (bs_l, uu____32166))
               | (bs1,c1) when
                   ((len < n1) && (FStar_Syntax_Util.is_total_comp c1)) &&
                     (let uu____32193 = FStar_Syntax_Util.has_decreases c1
                         in
                      Prims.op_Negation uu____32193)
                   ->
                   let uu____32195 =
                     aux true (n1 - len) (FStar_Syntax_Util.comp_result c1)
                      in
                   (match uu____32195 with
                    | (bs',c') -> ((FStar_List.append bs1 bs'), c'))
               | (bs1,c1) -> (bs1, c1))
           in
        aux true n t
  