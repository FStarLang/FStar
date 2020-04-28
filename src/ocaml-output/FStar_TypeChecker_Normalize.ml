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
        | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
            let uu____4597 =
              let uu____4598 = inline_closure_env cfg env1 [] t  in
              FStar_Syntax_Syntax.Meta uu____4598  in
            FStar_Pervasives_Native.Some uu____4597
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
        let uu____4615 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4699  ->
                  fun uu____4700  ->
                    match (uu____4699, uu____4700) with
                    | ((env2,out),(b,imp)) ->
                        let b1 =
                          let uu___579_4840 = b  in
                          let uu____4841 =
                            inline_closure_env cfg env2 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___579_4840.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___579_4840.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4841
                          }  in
                        let imp1 = close_imp cfg env2 imp  in
                        let env3 = dummy :: env2  in
                        (env3, ((b1, imp1) :: out))) (env1, []))
           in
        match uu____4615 with | (env2,bs1) -> ((FStar_List.rev bs1), env2)

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
        | uu____4983 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4996 = inline_closure_env cfg env1 [] t  in
                 let uu____4997 =
                   FStar_Option.map (norm_universe cfg env1) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4996 uu____4997
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____5010 = inline_closure_env cfg env1 [] t  in
                 let uu____5011 =
                   FStar_Option.map (norm_universe cfg env1) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____5010 uu____5011
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env1 []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____5065  ->
                           match uu____5065 with
                           | (a,q) ->
                               let uu____5086 =
                                 inline_closure_env cfg env1 [] a  in
                               (uu____5086, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_5103  ->
                           match uu___5_5103 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5107 =
                                 inline_closure_env cfg env1 [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5107
                           | f -> f))
                    in
                 let uu____5111 =
                   let uu___612_5112 = c1  in
                   let uu____5113 =
                     FStar_List.map (norm_universe cfg env1)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5113;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___612_5112.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5111)

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
                   (fun uu___6_5131  ->
                      match uu___6_5131 with
                      | FStar_Syntax_Syntax.DECREASES uu____5133 -> false
                      | uu____5137 -> true))
               in
            let rc1 =
              let uu___624_5140 = rc  in
              let uu____5141 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env1 [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___624_5140.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5141;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5150 -> lopt

let (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___7_5171  ->
            match uu___7_5171 with
            | FStar_Syntax_Syntax.DECREASES uu____5173 -> false
            | uu____5177 -> true))
  
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
    let uu____5224 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____5224 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5263 = FStar_Syntax_Embeddings.unembed e t  in
        uu____5263 false FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'uuuuuu5283 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'uuuuuu5283) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env1  ->
      FStar_List.fold_right
        (fun uu____5345  ->
           fun subst  ->
             match uu____5345 with
             | (binder_opt,closure1) ->
                 (match (binder_opt, closure1) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env2,term,uu____5386,uu____5387)) ->
                      let uu____5448 = b  in
                      (match uu____5448 with
                       | (bv,uu____5456) ->
                           let uu____5457 =
                             let uu____5459 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5459  in
                           if uu____5457
                           then subst
                           else
                             (let term1 = closure_as_term cfg env2 term  in
                              let uu____5467 = unembed_binder term1  in
                              match uu____5467 with
                              | FStar_Pervasives_Native.None  -> subst
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5474 =
                                      let uu___664_5475 = bv  in
                                      let uu____5476 =
                                        FStar_Syntax_Subst.subst subst
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___664_5475.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___664_5475.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5476
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5474
                                     in
                                  let b_for_x =
                                    let uu____5482 =
                                      let uu____5489 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5489)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5482  in
                                  let subst1 =
                                    FStar_List.filter
                                      (fun uu___8_5505  ->
                                         match uu___8_5505 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5507,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5509;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5510;_})
                                             ->
                                             let uu____5515 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5515
                                         | uu____5517 -> true) subst
                                     in
                                  b_for_x :: subst1))
                  | uu____5519 -> subst)) env1 []
  
let reduce_primops :
  'uuuuuu5541 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5541)
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
            (let uu____5593 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5593 with
             | (head,args) ->
                 let uu____5638 =
                   let uu____5639 = FStar_Syntax_Util.un_uinst head  in
                   uu____5639.FStar_Syntax_Syntax.n  in
                 (match uu____5638 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5645 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5645 with
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
                                (fun uu____5668  ->
                                   let uu____5669 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5671 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5673 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5669 uu____5671 uu____5673);
                              tm)
                           else
                             (let uu____5678 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5678 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5764  ->
                                        let uu____5765 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5765);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5770  ->
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
                                           (fun uu____5784  ->
                                              let uu____5785 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5785);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5793  ->
                                              let uu____5794 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5796 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5794 uu____5796);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5799 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5803  ->
                                 let uu____5804 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5804);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5810  ->
                            let uu____5811 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5811);
                       (match args with
                        | (a1,uu____5817)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5842 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5856  ->
                            let uu____5857 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5857);
                       (match args with
                        | (t,uu____5863)::(r,uu____5865)::[] ->
                            let uu____5906 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5906 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5912 -> tm))
                  | uu____5923 -> tm))
  
let reduce_equality :
  'uuuuuu5934 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'uuuuuu5934)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___752_5983 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___754_5986 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___754_5986.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___754_5986.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___754_5986.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.zeta_full =
                    (uu___754_5986.FStar_TypeChecker_Cfg.zeta_full);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___754_5986.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___754_5986.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___754_5986.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___754_5986.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___754_5986.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___754_5986.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___754_5986.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___754_5986.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___754_5986.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___754_5986.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___754_5986.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___754_5986.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___754_5986.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___754_5986.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___754_5986.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___754_5986.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___754_5986.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___754_5986.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___754_5986.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___754_5986.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___754_5986.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___754_5986.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___752_5983.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___752_5983.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___752_5983.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___752_5983.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___752_5983.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___752_5983.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___752_5983.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____5997 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____6008 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____6019 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd  ->
    fun args  ->
      let aux min_args =
        let uu____6040 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____6040
          (fun n  ->
             if n < min_args
             then Norm_request_none
             else
               if n = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____6072 =
        let uu____6073 = FStar_Syntax_Util.un_uinst hd  in
        uu____6073.FStar_Syntax_Syntax.n  in
      match uu____6072 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu____6082 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____6091 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____6091)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd  ->
    fun args  ->
      let uu____6104 =
        let uu____6105 = FStar_Syntax_Util.un_uinst hd  in
        uu____6105.FStar_Syntax_Syntax.n  in
      match uu____6104 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6163 = FStar_Syntax_Util.mk_app hd [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____6163 rest
           | uu____6190 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6230 = FStar_Syntax_Util.mk_app hd [t]  in
               FStar_Syntax_Util.mk_app uu____6230 rest
           | uu____6249 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____6323 = FStar_Syntax_Util.mk_app hd [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____6323 rest
           | uu____6358 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6360 ->
          let uu____6361 =
            let uu____6363 = FStar_Syntax_Print.term_to_string hd  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6363
             in
          failwith uu____6361
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6384  ->
    match uu___9_6384 with
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
        let uu____6391 =
          let uu____6394 =
            let uu____6395 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6395  in
          [uu____6394]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6391
    | FStar_Syntax_Embeddings.UnfoldFully names ->
        let uu____6403 =
          let uu____6406 =
            let uu____6407 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldFully uu____6407  in
          [uu____6406]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6403
    | FStar_Syntax_Embeddings.UnfoldAttr names ->
        let uu____6415 =
          let uu____6418 =
            let uu____6419 = FStar_List.map FStar_Ident.lid_of_str names  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6419  in
          [uu____6418]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6415
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s  ->
    let s1 = FStar_List.concatMap tr_norm_step s  in
    let add_exclude s2 z =
      let uu____6455 =
        FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2  in
      if uu____6455 then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2  in
    let s2 = FStar_TypeChecker_Env.Beta :: s1  in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta  in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota  in s4
  
let get_norm_request :
  'uuuuuu6480 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu6480) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6531 =
            let uu____6536 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6536 s  in
          match uu____6531 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6552 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6552
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
        | uu____6587::(tm,uu____6589)::[] ->
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
        | (tm,uu____6618)::[] ->
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
        | (steps,uu____6639)::uu____6640::(tm,uu____6642)::[] ->
            let uu____6663 =
              let uu____6668 = full_norm steps  in parse_steps uu____6668  in
            (match uu____6663 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s), tm))
        | uu____6698 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6730 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6737  ->
                    match uu___10_6737 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6739 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6741 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6745 -> true
                    | uu____6749 -> false))
             in
          if uu____6730
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6759  ->
             let uu____6760 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6760);
        (let tm_norm =
           let uu____6764 =
             let uu____6779 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6779.FStar_TypeChecker_Env.nbe  in
           uu____6764 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6783  ->
              let uu____6784 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6784);
         tm_norm)
  
let firstn :
  'uuuuuu6794 .
    Prims.int ->
      'uuuuuu6794 Prims.list ->
        ('uuuuuu6794 Prims.list * 'uuuuuu6794 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack1  ->
      let rec drop_irrel uu___11_6851 =
        match uu___11_6851 with
        | (MemoLazy uu____6856)::s -> drop_irrel s
        | (UnivArgs uu____6866)::s -> drop_irrel s
        | s -> s  in
      let uu____6879 = drop_irrel stack1  in
      match uu____6879 with
      | (App
          (uu____6883,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6884;
                        FStar_Syntax_Syntax.vars = uu____6885;_},uu____6886,uu____6887))::uu____6888
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6893 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6922) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6932) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6953  ->
                  match uu____6953 with
                  | (a,uu____6964) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6975 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6992 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6994 -> false
    | FStar_Syntax_Syntax.Tm_type uu____7008 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____7010 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____7012 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____7014 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____7016 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____7019 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____7027 -> false
    | FStar_Syntax_Syntax.Tm_let uu____7035 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____7050 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____7070 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____7086 -> true
    | FStar_Syntax_Syntax.Tm_match uu____7094 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7166  ->
                   match uu____7166 with
                   | (a,uu____7177) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7188) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____7287,args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7342  ->
                        match uu____7342 with
                        | (a,uu____7353) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7362,uu____7363,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7369,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7375 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7385 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7387 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7398 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7409 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7420 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7431 -> false
  
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
            let uu____7464 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7464 with
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
              (fun uu____7663  ->
                 fun uu____7664  ->
                   match (uu____7663, uu____7664) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7770 =
            match uu____7770 with
            | (x,y,z) ->
                let uu____7790 = FStar_Util.string_of_bool x  in
                let uu____7792 = FStar_Util.string_of_bool y  in
                let uu____7794 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7790 uu____7792
                  uu____7794
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7822  ->
                    let uu____7823 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7825 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7823 uu____7825);
               if b then reif else no)
            else
              if
                (let uu____7840 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7840)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7845  ->
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
                          ((is_rec,uu____7880),uu____7881);
                        FStar_Syntax_Syntax.sigrng = uu____7882;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7884;
                        FStar_Syntax_Syntax.sigattrs = uu____7885;
                        FStar_Syntax_Syntax.sigopts = uu____7886;_},uu____7887),uu____7888),uu____7889,uu____7890,uu____7891)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8000  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____8002,uu____8003,uu____8004,uu____8005) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8072  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____8075),uu____8076);
                        FStar_Syntax_Syntax.sigrng = uu____8077;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____8079;
                        FStar_Syntax_Syntax.sigattrs = uu____8080;
                        FStar_Syntax_Syntax.sigopts = uu____8081;_},uu____8082),uu____8083),uu____8084,uu____8085,uu____8086)
                     when
                     (is_rec &&
                        (Prims.op_Negation
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta))
                       &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8195  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8197,FStar_Pervasives_Native.Some
                    uu____8198,uu____8199,uu____8200) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8268  ->
                           let uu____8269 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8269);
                      (let uu____8272 =
                         let uu____8284 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8310 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8310
                            in
                         let uu____8322 =
                           let uu____8334 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8360 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8360
                              in
                           let uu____8376 =
                             let uu____8388 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8414 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8414
                                in
                             [uu____8388]  in
                           uu____8334 :: uu____8376  in
                         uu____8284 :: uu____8322  in
                       comb_or uu____8272))
                 | (uu____8462,uu____8463,FStar_Pervasives_Native.Some
                    uu____8464,uu____8465) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8533  ->
                           let uu____8534 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8534);
                      (let uu____8537 =
                         let uu____8549 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8575 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8575
                            in
                         let uu____8587 =
                           let uu____8599 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8625 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8625
                              in
                           let uu____8641 =
                             let uu____8653 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8679 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8679
                                in
                             [uu____8653]  in
                           uu____8599 :: uu____8641  in
                         uu____8549 :: uu____8587  in
                       comb_or uu____8537))
                 | (uu____8727,uu____8728,uu____8729,FStar_Pervasives_Native.Some
                    uu____8730) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8798  ->
                           let uu____8799 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8799);
                      (let uu____8802 =
                         let uu____8814 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8840 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8840
                            in
                         let uu____8852 =
                           let uu____8864 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8890 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8890
                              in
                           let uu____8906 =
                             let uu____8918 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8944 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8944
                                in
                             [uu____8918]  in
                           uu____8864 :: uu____8906  in
                         uu____8814 :: uu____8852  in
                       comb_or uu____8802))
                 | uu____8992 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____9038  ->
                           let uu____9039 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____9041 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____9043 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____9039 uu____9041 uu____9043);
                      (let uu____9046 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_9052  ->
                                 match uu___12_9052 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____9058 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____9058 l))
                          in
                       FStar_All.pipe_left yesno uu____9046)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____9074  ->
               let uu____9075 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____9077 =
                 let uu____9079 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____9079  in
               let uu____9080 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____9075 uu____9077 uu____9080);
          (match res with
           | (false ,uu____9083,uu____9084) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____9109 ->
               let uu____9119 =
                 let uu____9121 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9121
                  in
               FStar_All.pipe_left failwith uu____9119)
  
let decide_unfolding :
  'uuuuuu9140 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'uuuuuu9140 ->
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
                    let uu___1163_9209 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1165_9212 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1165_9212.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1165_9212.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1163_9209.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1163_9209.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1163_9209.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1163_9209.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1163_9209.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1163_9209.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1163_9209.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1163_9209.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____9274 = push e t  in (UnivArgs (us, r)) ::
                          uu____9274
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9286 =
                      let uu____9287 =
                        let uu____9288 = FStar_Syntax_Syntax.lid_of_fv fv  in
                        FStar_Const.Const_reflect uu____9288  in
                      FStar_Syntax_Syntax.Tm_constant uu____9287  in
                    FStar_Syntax_Syntax.mk uu____9286 FStar_Range.dummyRange
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
    let uu____9354 =
      let uu____9355 = FStar_Syntax_Subst.compress t  in
      uu____9355.FStar_Syntax_Syntax.n  in
    match uu____9354 with
    | FStar_Syntax_Syntax.Tm_app (hd,args) ->
        let uu____9386 =
          let uu____9387 = FStar_Syntax_Util.un_uinst hd  in
          uu____9387.FStar_Syntax_Syntax.n  in
        (match uu____9386 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9404 =
                 let uu____9411 =
                   let uu____9422 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9422 FStar_List.tl  in
                 FStar_All.pipe_right uu____9411 FStar_List.hd  in
               FStar_All.pipe_right uu____9404 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9521 -> FStar_Pervasives_Native.None)
    | uu____9522 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9801 ->
                   let uu____9816 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9816
               | uu____9819 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9829  ->
               let uu____9830 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9832 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9834 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9836 =
                 FStar_Util.string_of_int (FStar_List.length env1)  in
               let uu____9844 =
                 let uu____9846 =
                   let uu____9849 = firstn (Prims.of_int (4)) stack1  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9849
                    in
                 stack_to_string uu____9846  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9830 uu____9832 uu____9834 uu____9836 uu____9844);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9877  ->
               let uu____9878 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9878);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9884  ->
                     let uu____9885 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9885);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9888 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9892  ->
                     let uu____9893 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9893);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_name uu____9896 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9900  ->
                     let uu____9901 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9901);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9904 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9908  ->
                     let uu____9909 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9909);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9912;
                 FStar_Syntax_Syntax.fv_delta = uu____9913;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9917  ->
                     let uu____9918 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9918);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9921;
                 FStar_Syntax_Syntax.fv_delta = uu____9922;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9923);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9933  ->
                     let uu____9934 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9934);
                rebuild cfg env1 stack1 t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____9940 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____9940 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level uu____9943)
                    when uu____9943 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9947  ->
                          let uu____9948 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9948);
                     rebuild cfg env1 stack1 t1)
                | uu____9951 ->
                    let uu____9954 =
                      decide_unfolding cfg env1 stack1
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____9954 with
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
               let uu____9993 = closure_as_term cfg env1 t2  in
               rebuild cfg env1 stack1 uu____9993
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10021 = is_norm_request hd args  in
                  uu____10021 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____10027 = rejig_norm_request hd args  in
                 norm cfg env1 stack1 uu____10027))
           | FStar_Syntax_Syntax.Tm_app (hd,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10055 = is_norm_request hd args  in
                  uu____10055 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1276_10062 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1278_10065 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1278_10065.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1276_10062.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1276_10062.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1276_10062.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1276_10062.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1276_10062.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1276_10062.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____10072 =
                   get_norm_request cfg (norm cfg' env1 []) args  in
                 match uu____10072 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack2 =
                         FStar_All.pipe_right stack1
                           (FStar_List.fold_right
                              (fun uu____10108  ->
                                 fun stack2  ->
                                   match uu____10108 with
                                   | (a,aq) ->
                                       let uu____10120 =
                                         let uu____10121 =
                                           let uu____10128 =
                                             let uu____10129 =
                                               let uu____10161 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env1, a, uu____10161, false)
                                                in
                                             Clos uu____10129  in
                                           (uu____10128, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10121  in
                                       uu____10120 :: stack2) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10229  ->
                            let uu____10230 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10230);
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
                         let uu____10262 =
                           let uu____10264 =
                             let uu____10266 = FStar_Util.time_diff start fin
                                in
                             FStar_Pervasives_Native.snd uu____10266  in
                           FStar_Util.string_of_int uu____10264  in
                         let uu____10273 =
                           FStar_Syntax_Print.term_to_string tm'  in
                         let uu____10275 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                         let uu____10277 =
                           FStar_Syntax_Print.term_to_string tm_norm  in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____10262 uu____10273 uu____10275 uu____10277)
                      else ();
                      rebuild cfg env1 stack1 tm_norm)
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     let delta_level =
                       let uu____10297 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___13_10304  ->
                                 match uu___13_10304 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____10306 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____10308 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____10312 -> true
                                 | uu____10316 -> false))
                          in
                       if uu____10297
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let cfg'1 =
                       let uu___1316_10324 = cfg  in
                       let uu____10325 =
                         let uu___1318_10326 =
                           FStar_TypeChecker_Cfg.to_fsteps s  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.zeta_full =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.zeta_full);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1318_10326.FStar_TypeChecker_Cfg.for_extraction)
                         }  in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____10325;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1316_10324.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1316_10324.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1316_10324.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1316_10324.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1316_10324.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___1316_10324.FStar_TypeChecker_Cfg.reifying)
                       }  in
                     let stack' =
                       let tail = (Cfg cfg) :: stack1  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____10334 =
                           let uu____10335 =
                             let uu____10340 = FStar_Util.now ()  in
                             (tm, uu____10340)  in
                           Debug uu____10335  in
                         uu____10334 :: tail
                       else tail  in
                     norm cfg'1 env1 stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env1 u  in
               let uu____10345 =
                 FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env1 stack1 uu____10345
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env1 stack1 t'
               else
                 (let us1 =
                    let uu____10356 =
                      let uu____10363 =
                        FStar_List.map (norm_universe cfg env1) us  in
                      (uu____10363, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10356  in
                  let stack2 = us1 :: stack1  in norm cfg env1 stack2 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10372 = lookup_bvar env1 x  in
               (match uu____10372 with
                | Univ uu____10373 ->
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
                      let uu____10427 = FStar_ST.op_Bang r  in
                      (match uu____10427 with
                       | FStar_Pervasives_Native.Some (env3,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10523  ->
                                 let uu____10524 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10526 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10524
                                   uu____10526);
                            (let uu____10529 = maybe_weakly_reduced t'  in
                             if uu____10529
                             then
                               match stack1 with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env3 stack1 t'
                               | uu____10532 -> norm cfg env3 stack1 t'
                             else rebuild cfg env3 stack1 t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env2 ((MemoLazy r) :: stack1) t0)
                    else norm cfg env2 stack1 t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack1 with
                | (UnivArgs uu____10576)::uu____10577 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10588,uu____10589))::stack_rest ->
                    (match c with
                     | Univ uu____10593 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env1)
                           stack_rest t1
                     | uu____10602 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10632  ->
                                    let uu____10633 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10633);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env1) stack_rest body)
                          | b::tl ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10669  ->
                                    let uu____10670 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10670);
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
                       (fun uu____10718  ->
                          let uu____10719 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10719);
                     norm cfg env1 stack2 t1)
                | (Match uu____10722)::uu____10723 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10738 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10738 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____10774  -> dummy :: env2) env1)
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
                                          let uu____10818 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10818)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1440_10826 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1440_10826.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1440_10826.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10827 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10833  ->
                                 let uu____10834 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10834);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1447_10849 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1447_10849.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1447_10849.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1447_10849.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1447_10849.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1447_10849.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1447_10849.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1447_10849.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1447_10849.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Debug uu____10853)::uu____10854 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10865 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10865 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____10901  -> dummy :: env2) env1)
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
                                          let uu____10945 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10945)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1440_10953 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1440_10953.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1440_10953.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10954 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10960  ->
                                 let uu____10961 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10961);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1447_10976 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1447_10976.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1447_10976.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1447_10976.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1447_10976.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1447_10976.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1447_10976.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1447_10976.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1447_10976.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Meta uu____10980)::uu____10981 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____10994 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10994 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11030  -> dummy :: env2) env1)
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
                                          let uu____11074 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11074)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1440_11082 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1440_11082.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1440_11082.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11083 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11089  ->
                                 let uu____11090 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11090);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1447_11105 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1447_11105.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1447_11105.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1447_11105.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1447_11105.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1447_11105.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1447_11105.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1447_11105.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1447_11105.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Let uu____11109)::uu____11110 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11125 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11125 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11161  -> dummy :: env2) env1)
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
                                          let uu____11205 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11205)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1440_11213 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1440_11213.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1440_11213.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11214 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11220  ->
                                 let uu____11221 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11221);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1447_11236 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1447_11236.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1447_11236.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1447_11236.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1447_11236.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1447_11236.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1447_11236.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1447_11236.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1447_11236.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (App uu____11240)::uu____11241 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11256 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11256 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11292  -> dummy :: env2) env1)
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
                                          let uu____11336 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11336)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1440_11344 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1440_11344.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1440_11344.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11345 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11351  ->
                                 let uu____11352 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11352);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1447_11367 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1447_11367.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1447_11367.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1447_11367.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1447_11367.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1447_11367.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1447_11367.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1447_11367.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1447_11367.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (CBVApp uu____11371)::uu____11372 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11387 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11387 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11423  -> dummy :: env2) env1)
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
                                          let uu____11467 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11467)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1440_11475 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1440_11475.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1440_11475.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11476 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11482  ->
                                 let uu____11483 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11483);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1447_11498 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1447_11498.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1447_11498.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1447_11498.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1447_11498.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1447_11498.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1447_11498.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1447_11498.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1447_11498.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1)))
                | (Abs uu____11502)::uu____11503 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 t2
                    else
                      (let uu____11522 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11522 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11558  -> dummy :: env2) env1)
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
                                          let uu____11602 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11602)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1440_11610 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1440_11610.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1440_11610.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11611 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11617  ->
                                 let uu____11618 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11618);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1447_11633 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1447_11633.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1447_11633.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1447_11633.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1447_11633.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1447_11633.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1447_11633.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1447_11633.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1447_11633.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____11641 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11641 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env2  ->
                                     fun uu____11677  -> dummy :: env2) env1)
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
                                          let uu____11721 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11721)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1440_11729 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1440_11729.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1440_11729.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11730 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11736  ->
                                 let uu____11737 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11737);
                            (let stack2 = (Cfg cfg) :: stack1  in
                             let cfg1 =
                               let uu___1447_11752 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1447_11752.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1447_11752.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1447_11752.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1447_11752.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1447_11752.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1447_11752.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1447_11752.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1447_11752.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env1, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack2) body1))))
           | FStar_Syntax_Syntax.Tm_app (head,args) ->
               let strict_args =
                 let uu____11788 =
                   let uu____11789 = FStar_Syntax_Util.un_uinst head  in
                   uu____11789.FStar_Syntax_Syntax.n  in
                 match uu____11788 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11798 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack2 =
                      FStar_All.pipe_right stack1
                        (FStar_List.fold_right
                           (fun uu____11819  ->
                              fun stack2  ->
                                match uu____11819 with
                                | (a,aq) ->
                                    let uu____11831 =
                                      let uu____11832 =
                                        let uu____11839 =
                                          let uu____11840 =
                                            let uu____11872 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env1, a, uu____11872, false)  in
                                          Clos uu____11840  in
                                        (uu____11839, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11832  in
                                    uu____11831 :: stack2) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11940  ->
                          let uu____11941 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11941);
                     norm cfg env1 stack2 head)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____11992  ->
                              match uu____11992 with
                              | (a,i) ->
                                  let uu____12003 = norm cfg env1 [] a  in
                                  (uu____12003, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____12009 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____12024 = FStar_List.nth norm_args i
                                    in
                                 match uu____12024 with
                                 | (arg_i,uu____12035) ->
                                     let uu____12036 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____12036 with
                                      | (head1,uu____12055) ->
                                          let uu____12080 =
                                            let uu____12081 =
                                              FStar_Syntax_Util.un_uinst
                                                head1
                                               in
                                            uu____12081.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____12080 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____12085 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____12088 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____12088
                                           | uu____12089 -> false)))))
                       in
                    if uu____12009
                    then
                      let stack2 =
                        FStar_All.pipe_right stack1
                          (FStar_List.fold_right
                             (fun uu____12106  ->
                                fun stack2  ->
                                  match uu____12106 with
                                  | (a,aq) ->
                                      let uu____12118 =
                                        let uu____12119 =
                                          let uu____12126 =
                                            let uu____12127 =
                                              let uu____12159 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env1, a, uu____12159, false)
                                               in
                                            Clos uu____12127  in
                                          (uu____12126, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____12119  in
                                      uu____12118 :: stack2) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12241  ->
                            let uu____12242 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12242);
                       norm cfg env1 stack2 head)
                    else
                      (let head1 = closure_as_term cfg env1 head  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head1 norm_args
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env1 stack1 term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12260) when
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
                             ((let uu___1509_12305 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1509_12305.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1509_12305.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env1 stack1 t2
                  | uu____12306 ->
                      let uu____12321 = closure_as_term cfg env1 t1  in
                      rebuild cfg env1 stack1 uu____12321)
               else
                 (let t_x = norm cfg env1 [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12325 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12325 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env1) [] f1  in
                      let t2 =
                        let uu____12356 =
                          let uu____12357 =
                            let uu____12364 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1518_12370 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1518_12370.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1518_12370.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12364)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12357  in
                        FStar_Syntax_Syntax.mk uu____12356
                          t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12394 = closure_as_term cfg env1 t1  in
                 rebuild cfg env1 stack1 uu____12394
               else
                 (let uu____12397 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12397 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12405 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env2  ->
                                  fun uu____12431  -> dummy :: env2) env1)
                           in
                        norm_comp cfg uu____12405 c1  in
                      let t2 =
                        let uu____12455 = norm_binders cfg env1 bs1  in
                        FStar_Syntax_Util.arrow uu____12455 c2  in
                      rebuild cfg env1 stack1 t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env1 stack1 t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack1 with
                | (Match uu____12568)::uu____12569 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12582  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (Arg uu____12584)::uu____12585 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12596  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (App
                    (uu____12598,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12599;
                                   FStar_Syntax_Syntax.vars = uu____12600;_},uu____12601,uu____12602))::uu____12603
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12610  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | (MemoLazy uu____12612)::uu____12613 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12624  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env1 stack1 t11)
                | uu____12626 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12629  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env1 [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12634  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12660 = norm cfg env1 [] t2  in
                             FStar_Util.Inl uu____12660
                         | FStar_Util.Inr c ->
                             let uu____12674 = norm_comp cfg env1 c  in
                             FStar_Util.Inr uu____12674
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env1 [])  in
                       match stack1 with
                       | (Cfg cfg1)::stack2 ->
                           let t2 =
                             let uu____12697 =
                               let uu____12698 =
                                 let uu____12725 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12725, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12698
                                in
                             FStar_Syntax_Syntax.mk uu____12697
                               t1.FStar_Syntax_Syntax.pos
                              in
                           norm cfg1 env1 stack2 t2
                       | uu____12760 ->
                           let uu____12761 =
                             let uu____12762 =
                               let uu____12763 =
                                 let uu____12790 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12790, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12763
                                in
                             FStar_Syntax_Syntax.mk uu____12762
                               t1.FStar_Syntax_Syntax.pos
                              in
                           rebuild cfg env1 stack1 uu____12761))))
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
                   let uu___1597_12868 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1599_12871 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.zeta_full =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.zeta_full);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1599_12871.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1597_12868.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1597_12868.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1597_12868.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1597_12868.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1597_12868.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1597_12868.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1597_12868.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1597_12868.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____12912 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12912 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1612_12932 = cfg  in
                               let uu____12933 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1612_12932.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12933;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1612_12932.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1612_12932.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1612_12932.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1612_12932.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1612_12932.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1612_12932.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1612_12932.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____12940 =
                                 let uu____12941 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env1 [] uu____12941  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12940
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1619_12944 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1619_12944.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1619_12944.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1619_12944.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1619_12944.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12945 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env1 stack1 uu____12945
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12958,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12959;
                               FStar_Syntax_Syntax.lbunivs = uu____12960;
                               FStar_Syntax_Syntax.lbtyp = uu____12961;
                               FStar_Syntax_Syntax.lbeff = uu____12962;
                               FStar_Syntax_Syntax.lbdef = uu____12963;
                               FStar_Syntax_Syntax.lbattrs = uu____12964;
                               FStar_Syntax_Syntax.lbpos = uu____12965;_}::uu____12966),uu____12967)
               -> rebuild cfg env1 stack1 t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let uu____13012 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
               if uu____13012
               then
                 let binder =
                   let uu____13016 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____13016  in
                 let def =
                   FStar_Syntax_Util.unmeta_lift lb.FStar_Syntax_Syntax.lbdef
                    in
                 let env2 =
                   let uu____13027 =
                     let uu____13034 =
                       let uu____13035 =
                         let uu____13067 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env1, def, uu____13067, false)  in
                       Clos uu____13035  in
                     ((FStar_Pervasives_Native.Some binder), uu____13034)  in
                   uu____13027 :: env1  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____13142  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env2 stack1 body)
               else
                 (let uu____13146 =
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
                      &&
                      (let uu____13149 =
                         FStar_TypeChecker_Env.norm_eff_name
                           cfg.FStar_TypeChecker_Cfg.tcenv
                           lb.FStar_Syntax_Syntax.lbeff
                          in
                       FStar_Syntax_Util.is_div_effect uu____13149)
                     in
                  if uu____13146
                  then
                    let ffun =
                      let uu____13154 =
                        let uu____13155 =
                          let uu____13174 =
                            let uu____13183 =
                              let uu____13190 =
                                FStar_All.pipe_right
                                  lb.FStar_Syntax_Syntax.lbname
                                  FStar_Util.left
                                 in
                              FStar_Syntax_Syntax.mk_binder uu____13190  in
                            [uu____13183]  in
                          (uu____13174, body, FStar_Pervasives_Native.None)
                           in
                        FStar_Syntax_Syntax.Tm_abs uu____13155  in
                      FStar_Syntax_Syntax.mk uu____13154
                        t1.FStar_Syntax_Syntax.pos
                       in
                    let stack2 =
                      (CBVApp
                         (env1, ffun, FStar_Pervasives_Native.None,
                           (t1.FStar_Syntax_Syntax.pos)))
                      :: stack1  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____13224  ->
                          FStar_Util.print_string
                            "+++ Evaluating DIV Tm_let\n");
                     norm cfg env1 stack2 lb.FStar_Syntax_Syntax.lbdef)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____13231  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____13233 = closure_as_term cfg env1 t1  in
                        rebuild cfg env1 stack1 uu____13233))
                    else
                      (let uu____13236 =
                         let uu____13241 =
                           let uu____13242 =
                             let uu____13249 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____13249
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____13242]  in
                         FStar_Syntax_Subst.open_term uu____13241 body  in
                       match uu____13236 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____13276  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____13285 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____13285  in
                               FStar_Util.Inl
                                 (let uu___1666_13301 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1666_13301.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1666_13301.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____13304  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1671_13307 = lb  in
                                let uu____13308 =
                                  norm cfg env1 []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____13311 =
                                  FStar_List.map (norm cfg env1 [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1671_13307.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1671_13307.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____13308;
                                  FStar_Syntax_Syntax.lbattrs = uu____13311;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1671_13307.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____13346  -> dummy :: env2)
                                     env1)
                                 in
                              let stack2 = (Cfg cfg) :: stack1  in
                              let cfg1 =
                                let uu___1678_13371 = cfg  in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1678_13371.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1678_13371.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1678_13371.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1678_13371.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1678_13371.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1678_13371.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1678_13371.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1678_13371.FStar_TypeChecker_Cfg.reifying)
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____13375  ->
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
               let uu____13396 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13396 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env1 [] lb.FStar_Syntax_Syntax.lbtyp
                              in
                           let lbname =
                             let uu____13432 =
                               let uu___1694_13433 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1694_13433.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1694_13433.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13432  in
                           let uu____13434 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13434 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env1 xs  in
                               let env2 =
                                 let uu____13460 =
                                   FStar_List.map (fun uu____13482  -> dummy)
                                     xs1
                                    in
                                 let uu____13489 =
                                   let uu____13498 =
                                     FStar_List.map
                                       (fun uu____13514  -> dummy) lbs1
                                      in
                                   FStar_List.append uu____13498 env1  in
                                 FStar_List.append uu____13460 uu____13489
                                  in
                               let def_body1 = norm cfg env2 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13534 =
                                       let uu___1708_13535 = rc  in
                                       let uu____13536 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env2 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1708_13535.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13536;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1708_13535.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13534
                                 | uu____13545 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1713_13551 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1713_13551.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1713_13551.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1713_13551.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1713_13551.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13561 =
                        FStar_List.map (fun uu____13577  -> dummy) lbs2  in
                      FStar_List.append uu____13561 env1  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13585 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13585 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1722_13601 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1722_13601.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1722_13601.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env1 stack1 t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               (Prims.op_Negation
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                 &&
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta_full)
               ->
               let uu____13635 = closure_as_term cfg env1 t1  in
               rebuild cfg env1 stack1 uu____13635
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13656 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13734  ->
                        match uu____13734 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1738_13859 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1738_13859.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1738_13859.FStar_Syntax_Syntax.sort)
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
               (match uu____13656 with
                | (rec_env,memos,uu____14050) ->
                    let uu____14105 =
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
                             let uu____14354 =
                               let uu____14361 =
                                 let uu____14362 =
                                   let uu____14394 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14394, false)
                                    in
                                 Clos uu____14362  in
                               (FStar_Pervasives_Native.None, uu____14361)
                                in
                             uu____14354 :: env2)
                        (FStar_Pervasives_Native.snd lbs) env1
                       in
                    norm cfg body_env stack1 body)
           | FStar_Syntax_Syntax.Tm_meta (head,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14479  ->
                     let uu____14480 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14480);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env1 stack1 head
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14504 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env1 stack1 head
                     else
                       (match stack1 with
                        | uu____14508::uu____14509 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14514) ->
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
                             | uu____14593 -> norm cfg env1 stack1 head)
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
                                  let uu____14641 =
                                    let uu____14662 =
                                      norm_pattern_args cfg env1 args  in
                                    (names1, uu____14662)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14641
                              | uu____14691 -> m  in
                            let t2 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_meta (head1, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env1 stack1 t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14697 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env1 stack1 t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14713 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14727 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14741 =
                        let uu____14743 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14745 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14743 uu____14745
                         in
                      failwith uu____14741
                    else
                      (let uu____14750 = inline_closure_env cfg env1 [] t2
                          in
                       rebuild cfg env1 stack1 uu____14750)
                | uu____14751 -> norm cfg env1 stack1 t2))

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
              let uu____14760 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14760 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14774  ->
                        let uu____14775 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14775);
                   rebuild cfg env1 stack1 t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14788  ->
                        let uu____14789 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14791 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14789 uu____14791);
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
                      | (UnivArgs (us',uu____14804))::stack2 ->
                          ((let uu____14813 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14813
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14821 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14821) us'
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
                      | uu____14857 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env1 stack1 t1
                      | uu____14860 ->
                          let uu____14863 =
                            let uu____14865 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14865
                             in
                          failwith uu____14863
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
              let uu____14885 =
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
                    let uu___1849_14903 = cfg  in
                    let uu____14904 =
                      FStar_List.fold_right
                        FStar_TypeChecker_Cfg.fstep_add_one new_steps
                        cfg.FStar_TypeChecker_Cfg.steps
                       in
                    {
                      FStar_TypeChecker_Cfg.steps = uu____14904;
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1849_14903.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1849_14903.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        [FStar_TypeChecker_Env.InliningDelta;
                        FStar_TypeChecker_Env.Eager_unfolding_only];
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1849_14903.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1849_14903.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1849_14903.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1849_14903.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1849_14903.FStar_TypeChecker_Cfg.reifying)
                    }  in
                  (cfg', ((Cfg cfg) :: stack1))
                else (cfg, stack1)  in
              match uu____14885 with
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
                     (uu____14945,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14946;
                                    FStar_Syntax_Syntax.vars = uu____14947;_},uu____14948,uu____14949))::uu____14950
                     -> ()
                 | uu____14955 ->
                     let uu____14958 =
                       let uu____14960 = stack_to_string stack1  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14960
                        in
                     failwith uu____14958);
                (let top0 = top  in
                 let top1 = FStar_Syntax_Util.unascribe top  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____14969  ->
                      let uu____14970 = FStar_Syntax_Print.tag_of_term top1
                         in
                      let uu____14972 =
                        FStar_Syntax_Print.term_to_string top1  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____14970
                        uu____14972);
                 (let top2 = FStar_Syntax_Util.unmeta_safe top1  in
                  let uu____14976 =
                    let uu____14977 = FStar_Syntax_Subst.compress top2  in
                    uu____14977.FStar_Syntax_Syntax.n  in
                  match uu____14976 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let eff_name =
                        FStar_TypeChecker_Env.norm_eff_name
                          cfg.FStar_TypeChecker_Cfg.tcenv m
                         in
                      let ed =
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv eff_name
                         in
                      let uu____14999 =
                        let uu____15008 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_eff_repr
                           in
                        FStar_All.pipe_right uu____15008 FStar_Util.must  in
                      (match uu____14999 with
                       | (uu____15023,repr) ->
                           let uu____15033 =
                             let uu____15040 =
                               FStar_All.pipe_right ed
                                 FStar_Syntax_Util.get_bind_repr
                                in
                             FStar_All.pipe_right uu____15040 FStar_Util.must
                              in
                           (match uu____15033 with
                            | (uu____15077,bind_repr) ->
                                (match lb.FStar_Syntax_Syntax.lbname with
                                 | FStar_Util.Inr uu____15083 ->
                                     failwith
                                       "Cannot reify a top-level let binding"
                                 | FStar_Util.Inl x ->
                                     let is_return e =
                                       let uu____15094 =
                                         let uu____15095 =
                                           FStar_Syntax_Subst.compress e  in
                                         uu____15095.FStar_Syntax_Syntax.n
                                          in
                                       match uu____15094 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e1,FStar_Syntax_Syntax.Meta_monadic
                                            (uu____15101,uu____15102))
                                           ->
                                           let uu____15111 =
                                             let uu____15112 =
                                               FStar_Syntax_Subst.compress e1
                                                in
                                             uu____15112.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____15111 with
                                            | FStar_Syntax_Syntax.Tm_meta
                                                (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                                 (uu____15118,msrc,uu____15120))
                                                when
                                                FStar_Syntax_Util.is_pure_effect
                                                  msrc
                                                ->
                                                let uu____15129 =
                                                  FStar_Syntax_Subst.compress
                                                    e2
                                                   in
                                                FStar_Pervasives_Native.Some
                                                  uu____15129
                                            | uu____15130 ->
                                                FStar_Pervasives_Native.None)
                                       | uu____15131 ->
                                           FStar_Pervasives_Native.None
                                        in
                                     let uu____15132 =
                                       is_return lb.FStar_Syntax_Syntax.lbdef
                                        in
                                     (match uu____15132 with
                                      | FStar_Pervasives_Native.Some e ->
                                          let lb1 =
                                            let uu___1928_15137 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (uu___1928_15137.FStar_Syntax_Syntax.lbname);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___1928_15137.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___1928_15137.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.lbdef = e;
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___1928_15137.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___1928_15137.FStar_Syntax_Syntax.lbpos)
                                            }  in
                                          let uu____15138 =
                                            FStar_List.tl stack1  in
                                          let uu____15139 =
                                            let uu____15140 =
                                              let uu____15141 =
                                                let uu____15155 =
                                                  FStar_Syntax_Util.mk_reify
                                                    body
                                                   in
                                                ((false, [lb1]), uu____15155)
                                                 in
                                              FStar_Syntax_Syntax.Tm_let
                                                uu____15141
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____15140
                                              top2.FStar_Syntax_Syntax.pos
                                             in
                                          norm cfg env1 uu____15138
                                            uu____15139
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____15171 =
                                            let uu____15173 = is_return body
                                               in
                                            match uu____15173 with
                                            | FStar_Pervasives_Native.Some
                                                {
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_bvar
                                                    y;
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____15178;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____15179;_}
                                                ->
                                                FStar_Syntax_Syntax.bv_eq x y
                                            | uu____15182 -> false  in
                                          if uu____15171
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
                                             let uu____15197 =
                                               let bv =
                                                 FStar_Syntax_Syntax.new_bv
                                                   FStar_Pervasives_Native.None
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               let lb1 =
                                                 let uu____15206 =
                                                   let uu____15209 =
                                                     let uu____15220 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         x.FStar_Syntax_Syntax.sort
                                                        in
                                                     [uu____15220]  in
                                                   FStar_Syntax_Util.mk_app
                                                     repr uu____15209
                                                    in
                                                 let uu____15245 =
                                                   let uu____15246 =
                                                     FStar_TypeChecker_Env.is_total_effect
                                                       cfg.FStar_TypeChecker_Cfg.tcenv
                                                       eff_name
                                                      in
                                                   if uu____15246
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
                                                     = uu____15206;
                                                   FStar_Syntax_Syntax.lbeff
                                                     = uu____15245;
                                                   FStar_Syntax_Syntax.lbdef
                                                     = head;
                                                   FStar_Syntax_Syntax.lbattrs
                                                     = [];
                                                   FStar_Syntax_Syntax.lbpos
                                                     =
                                                     (head.FStar_Syntax_Syntax.pos)
                                                 }  in
                                               let uu____15253 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   bv
                                                  in
                                               (lb1, bv, uu____15253)  in
                                             match uu____15197 with
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
                                                   let uu____15270 =
                                                     let uu____15271 =
                                                       let uu____15290 =
                                                         let uu____15299 =
                                                           FStar_Syntax_Syntax.mk_binder
                                                             x
                                                            in
                                                         [uu____15299]  in
                                                       (uu____15290, body1,
                                                         (FStar_Pervasives_Native.Some
                                                            body_rc))
                                                        in
                                                     FStar_Syntax_Syntax.Tm_abs
                                                       uu____15271
                                                      in
                                                   FStar_Syntax_Syntax.mk
                                                     uu____15270
                                                     body1.FStar_Syntax_Syntax.pos
                                                    in
                                                 let close =
                                                   closure_as_term cfg env1
                                                    in
                                                 let bind_inst =
                                                   let uu____15338 =
                                                     let uu____15339 =
                                                       FStar_Syntax_Subst.compress
                                                         bind_repr
                                                        in
                                                     uu____15339.FStar_Syntax_Syntax.n
                                                      in
                                                   match uu____15338 with
                                                   | FStar_Syntax_Syntax.Tm_uinst
                                                       (bind,uu____15345::uu____15346::[])
                                                       ->
                                                       let uu____15351 =
                                                         let uu____15352 =
                                                           let uu____15359 =
                                                             let uu____15360
                                                               =
                                                               let uu____15361
                                                                 =
                                                                 close
                                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                                  in
                                                               (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                                 uu____15361
                                                                in
                                                             let uu____15362
                                                               =
                                                               let uu____15365
                                                                 =
                                                                 let uu____15366
                                                                   = 
                                                                   close t
                                                                    in
                                                                 (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                                   cfg.FStar_TypeChecker_Cfg.tcenv
                                                                   uu____15366
                                                                  in
                                                               [uu____15365]
                                                                in
                                                             uu____15360 ::
                                                               uu____15362
                                                              in
                                                           (bind,
                                                             uu____15359)
                                                            in
                                                         FStar_Syntax_Syntax.Tm_uinst
                                                           uu____15352
                                                          in
                                                       FStar_Syntax_Syntax.mk
                                                         uu____15351 rng
                                                   | uu____15369 ->
                                                       failwith
                                                         "NIY : Reification of indexed effects"
                                                    in
                                                 let maybe_range_arg =
                                                   let uu____15384 =
                                                     FStar_Util.for_some
                                                       (FStar_Syntax_Util.attr_eq
                                                          FStar_Syntax_Util.dm4f_bind_range_attr)
                                                       ed.FStar_Syntax_Syntax.eff_attrs
                                                      in
                                                   if uu____15384
                                                   then
                                                     let uu____15397 =
                                                       let uu____15406 =
                                                         FStar_TypeChecker_Cfg.embed_simple
                                                           FStar_Syntax_Embeddings.e_range
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                           lb.FStar_Syntax_Syntax.lbpos
                                                          in
                                                       FStar_Syntax_Syntax.as_arg
                                                         uu____15406
                                                        in
                                                     let uu____15407 =
                                                       let uu____15418 =
                                                         let uu____15427 =
                                                           FStar_TypeChecker_Cfg.embed_simple
                                                             FStar_Syntax_Embeddings.e_range
                                                             body2.FStar_Syntax_Syntax.pos
                                                             body2.FStar_Syntax_Syntax.pos
                                                            in
                                                         FStar_Syntax_Syntax.as_arg
                                                           uu____15427
                                                          in
                                                       [uu____15418]  in
                                                     uu____15397 ::
                                                       uu____15407
                                                   else []  in
                                                 let reified =
                                                   let args =
                                                     let uu____15476 =
                                                       FStar_Syntax_Util.is_layered
                                                         ed
                                                        in
                                                     if uu____15476
                                                     then
                                                       let unit_args =
                                                         let uu____15500 =
                                                           let uu____15501 =
                                                             let uu____15504
                                                               =
                                                               let uu____15505
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   ed
                                                                   FStar_Syntax_Util.get_bind_vc_combinator
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15505
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15504
                                                               FStar_Syntax_Subst.compress
                                                              in
                                                           uu____15501.FStar_Syntax_Syntax.n
                                                            in
                                                         match uu____15500
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_arrow
                                                             (uu____15546::uu____15547::bs,uu____15549)
                                                             when
                                                             (FStar_List.length
                                                                bs)
                                                               >=
                                                               (Prims.of_int (2))
                                                             ->
                                                             let uu____15601
                                                               =
                                                               let uu____15610
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   bs
                                                                   (FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs) -
                                                                    (Prims.of_int (2))))
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____15610
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____15601
                                                               (FStar_List.map
                                                                  (fun
                                                                    uu____15741
                                                                     ->
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.unit_const))
                                                         | uu____15748 ->
                                                             let uu____15749
                                                               =
                                                               let uu____15755
                                                                 =
                                                                 let uu____15757
                                                                   =
                                                                   FStar_Ident.string_of_lid
                                                                    ed.FStar_Syntax_Syntax.mname
                                                                    in
                                                                 let uu____15759
                                                                   =
                                                                   let uu____15761
                                                                    =
                                                                    let uu____15762
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    ed
                                                                    FStar_Syntax_Util.get_bind_vc_combinator
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15762
                                                                    FStar_Pervasives_Native.snd
                                                                     in
                                                                   FStar_All.pipe_right
                                                                    uu____15761
                                                                    FStar_Syntax_Print.term_to_string
                                                                    in
                                                                 FStar_Util.format2
                                                                   "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                                   uu____15757
                                                                   uu____15759
                                                                  in
                                                               (FStar_Errors.Fatal_UnexpectedEffect,
                                                                 uu____15755)
                                                                in
                                                             FStar_Errors.raise_error
                                                               uu____15749
                                                               rng
                                                          in
                                                       let uu____15796 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           lb.FStar_Syntax_Syntax.lbtyp
                                                          in
                                                       let uu____15805 =
                                                         let uu____15816 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             t
                                                            in
                                                         let uu____15825 =
                                                           let uu____15836 =
                                                             let uu____15847
                                                               =
                                                               FStar_Syntax_Syntax.as_arg
                                                                 head1
                                                                in
                                                             let uu____15856
                                                               =
                                                               let uu____15867
                                                                 =
                                                                 FStar_Syntax_Syntax.as_arg
                                                                   body2
                                                                  in
                                                               [uu____15867]
                                                                in
                                                             uu____15847 ::
                                                               uu____15856
                                                              in
                                                           FStar_List.append
                                                             unit_args
                                                             uu____15836
                                                            in
                                                         uu____15816 ::
                                                           uu____15825
                                                          in
                                                       uu____15796 ::
                                                         uu____15805
                                                     else
                                                       (let uu____15926 =
                                                          let uu____15937 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              lb.FStar_Syntax_Syntax.lbtyp
                                                             in
                                                          let uu____15946 =
                                                            let uu____15957 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                t
                                                               in
                                                            [uu____15957]  in
                                                          uu____15937 ::
                                                            uu____15946
                                                           in
                                                        let uu____15990 =
                                                          let uu____16001 =
                                                            let uu____16012 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                FStar_Syntax_Syntax.tun
                                                               in
                                                            let uu____16021 =
                                                              let uu____16032
                                                                =
                                                                FStar_Syntax_Syntax.as_arg
                                                                  head1
                                                                 in
                                                              let uu____16041
                                                                =
                                                                let uu____16052
                                                                  =
                                                                  FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Syntax.tun
                                                                   in
                                                                let uu____16061
                                                                  =
                                                                  let uu____16072
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    body2  in
                                                                  [uu____16072]
                                                                   in
                                                                uu____16052
                                                                  ::
                                                                  uu____16061
                                                                 in
                                                              uu____16032 ::
                                                                uu____16041
                                                               in
                                                            uu____16012 ::
                                                              uu____16021
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____16001
                                                           in
                                                        FStar_List.append
                                                          uu____15926
                                                          uu____15990)
                                                      in
                                                   let uu____16137 =
                                                     let uu____16138 =
                                                       let uu____16152 =
                                                         let uu____16155 =
                                                           let uu____16162 =
                                                             let uu____16163
                                                               =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 head_bv
                                                                in
                                                             [uu____16163]
                                                              in
                                                           FStar_Syntax_Subst.close
                                                             uu____16162
                                                            in
                                                         let uu____16182 =
                                                           FStar_Syntax_Syntax.mk
                                                             (FStar_Syntax_Syntax.Tm_app
                                                                (bind_inst,
                                                                  args)) rng
                                                            in
                                                         FStar_All.pipe_left
                                                           uu____16155
                                                           uu____16182
                                                          in
                                                       ((false, [lb_head]),
                                                         uu____16152)
                                                        in
                                                     FStar_Syntax_Syntax.Tm_let
                                                       uu____16138
                                                      in
                                                   FStar_Syntax_Syntax.mk
                                                     uu____16137 rng
                                                    in
                                                 (FStar_TypeChecker_Cfg.log
                                                    cfg
                                                    (fun uu____16214  ->
                                                       let uu____16215 =
                                                         FStar_Syntax_Print.term_to_string
                                                           top0
                                                          in
                                                       let uu____16217 =
                                                         FStar_Syntax_Print.term_to_string
                                                           reified
                                                          in
                                                       FStar_Util.print2
                                                         "Reified (1) <%s> to %s\n"
                                                         uu____16215
                                                         uu____16217);
                                                  (let uu____16220 =
                                                     FStar_List.tl stack1  in
                                                   norm cfg env1 uu____16220
                                                     reified)))))))
                  | FStar_Syntax_Syntax.Tm_app (head,args) ->
                      ((let uu____16248 = FStar_Options.defensive ()  in
                        if uu____16248
                        then
                          let is_arg_impure uu____16263 =
                            match uu____16263 with
                            | (e,q) ->
                                let uu____16277 =
                                  let uu____16278 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16278.FStar_Syntax_Syntax.n  in
                                (match uu____16277 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____16294 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____16294
                                 | uu____16296 -> false)
                             in
                          let uu____16298 =
                            let uu____16300 =
                              let uu____16311 =
                                FStar_Syntax_Syntax.as_arg head  in
                              uu____16311 :: args  in
                            FStar_Util.for_some is_arg_impure uu____16300  in
                          (if uu____16298
                           then
                             let uu____16337 =
                               let uu____16343 =
                                 let uu____16345 =
                                   FStar_Syntax_Print.term_to_string top2  in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____16345
                                  in
                               (FStar_Errors.Warning_Defensive, uu____16343)
                                in
                             FStar_Errors.log_issue
                               top2.FStar_Syntax_Syntax.pos uu____16337
                           else ())
                        else ());
                       (let fallback1 uu____16358 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16362  ->
                               let uu____16363 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____16363 "");
                          (let uu____16367 = FStar_List.tl stack1  in
                           let uu____16368 = FStar_Syntax_Util.mk_reify top2
                              in
                           norm cfg env1 uu____16367 uu____16368)
                           in
                        let fallback2 uu____16374 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16378  ->
                               let uu____16379 =
                                 FStar_Syntax_Print.term_to_string top0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____16379 "");
                          (let uu____16383 = FStar_List.tl stack1  in
                           let uu____16384 =
                             FStar_Syntax_Syntax.mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (top2,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               top0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env1 uu____16383 uu____16384)
                           in
                        let uu____16389 =
                          let uu____16390 = FStar_Syntax_Util.un_uinst head
                             in
                          uu____16390.FStar_Syntax_Syntax.n  in
                        match uu____16389 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____16396 =
                              let uu____16398 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____16398  in
                            if uu____16396
                            then fallback1 ()
                            else
                              (let uu____16403 =
                                 let uu____16405 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____16405  in
                               if uu____16403
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____16420 =
                                      FStar_Syntax_Util.mk_reify head  in
                                    FStar_Syntax_Syntax.mk_Tm_app uu____16420
                                      args t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____16421 = FStar_List.tl stack1  in
                                  norm cfg env1 uu____16421 t1))
                        | uu____16422 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____16424) ->
                      do_reify_monadic fallback cfg env1 stack1 e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____16448 = closure_as_term cfg env1 t'  in
                        reify_lift cfg e msrc mtgt uu____16448  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____16452  ->
                            let uu____16453 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____16453);
                       (let uu____16456 = FStar_List.tl stack1  in
                        norm cfg env1 uu____16456 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches1) ->
                      let branches2 =
                        FStar_All.pipe_right branches1
                          (FStar_List.map
                             (fun uu____16577  ->
                                match uu____16577 with
                                | (pat,wopt,tm) ->
                                    let uu____16625 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16625)))
                         in
                      let tm =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_match (e, branches2))
                          top2.FStar_Syntax_Syntax.pos
                         in
                      let uu____16657 = FStar_List.tl stack1  in
                      norm cfg env1 uu____16657 tm
                  | uu____16658 -> fallback ()))

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
              (fun uu____16672  ->
                 let uu____16673 = FStar_Ident.string_of_lid msrc  in
                 let uu____16675 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16677 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16673
                   uu____16675 uu____16677);
            (let uu____16680 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16683 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env1)
                     in
                  Prims.op_Negation uu____16683)
                in
             if uu____16680
             then
               let ed =
                 let uu____16688 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env1 uu____16688  in
               let uu____16689 =
                 let uu____16698 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
                 FStar_All.pipe_right uu____16698 FStar_Util.must  in
               match uu____16689 with
               | (uu____16745,repr) ->
                   let uu____16755 =
                     let uu____16764 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_return_repr
                        in
                     FStar_All.pipe_right uu____16764 FStar_Util.must  in
                   (match uu____16755 with
                    | (uu____16811,return_repr) ->
                        let return_inst =
                          let uu____16824 =
                            let uu____16825 =
                              FStar_Syntax_Subst.compress return_repr  in
                            uu____16825.FStar_Syntax_Syntax.n  in
                          match uu____16824 with
                          | FStar_Syntax_Syntax.Tm_uinst
                              (return_tm,uu____16831::[]) ->
                              let uu____16836 =
                                let uu____16837 =
                                  let uu____16844 =
                                    let uu____16845 =
                                      env1.FStar_TypeChecker_Env.universe_of
                                        env1 t
                                       in
                                    [uu____16845]  in
                                  (return_tm, uu____16844)  in
                                FStar_Syntax_Syntax.Tm_uinst uu____16837  in
                              FStar_Syntax_Syntax.mk uu____16836
                                e.FStar_Syntax_Syntax.pos
                          | uu____16848 ->
                              failwith "NIY : Reification of indexed effects"
                           in
                        let uu____16852 =
                          let bv =
                            FStar_Syntax_Syntax.new_bv
                              FStar_Pervasives_Native.None t
                             in
                          let lb =
                            let uu____16863 =
                              let uu____16866 =
                                let uu____16877 =
                                  FStar_Syntax_Syntax.as_arg t  in
                                [uu____16877]  in
                              FStar_Syntax_Util.mk_app repr uu____16866  in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (FStar_Util.Inl bv);
                              FStar_Syntax_Syntax.lbunivs = [];
                              FStar_Syntax_Syntax.lbtyp = uu____16863;
                              FStar_Syntax_Syntax.lbeff = msrc;
                              FStar_Syntax_Syntax.lbdef = e;
                              FStar_Syntax_Syntax.lbattrs = [];
                              FStar_Syntax_Syntax.lbpos =
                                (e.FStar_Syntax_Syntax.pos)
                            }  in
                          let uu____16904 = FStar_Syntax_Syntax.bv_to_name bv
                             in
                          (lb, bv, uu____16904)  in
                        (match uu____16852 with
                         | (lb_e,e_bv,e1) ->
                             let uu____16916 =
                               let uu____16917 =
                                 let uu____16931 =
                                   let uu____16934 =
                                     let uu____16941 =
                                       let uu____16942 =
                                         FStar_Syntax_Syntax.mk_binder e_bv
                                          in
                                       [uu____16942]  in
                                     FStar_Syntax_Subst.close uu____16941  in
                                   let uu____16961 =
                                     let uu____16962 =
                                       let uu____16963 =
                                         let uu____16980 =
                                           let uu____16991 =
                                             FStar_Syntax_Syntax.as_arg t  in
                                           let uu____17000 =
                                             let uu____17011 =
                                               FStar_Syntax_Syntax.as_arg e1
                                                in
                                             [uu____17011]  in
                                           uu____16991 :: uu____17000  in
                                         (return_inst, uu____16980)  in
                                       FStar_Syntax_Syntax.Tm_app uu____16963
                                        in
                                     FStar_Syntax_Syntax.mk uu____16962
                                       e1.FStar_Syntax_Syntax.pos
                                      in
                                   FStar_All.pipe_left uu____16934
                                     uu____16961
                                    in
                                 ((false, [lb_e]), uu____16931)  in
                               FStar_Syntax_Syntax.Tm_let uu____16917  in
                             FStar_Syntax_Syntax.mk uu____16916
                               e1.FStar_Syntax_Syntax.pos))
             else
               (let uu____17073 =
                  FStar_TypeChecker_Env.monad_leq env1 msrc mtgt  in
                match uu____17073 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17076 =
                      let uu____17078 = FStar_Ident.string_of_lid msrc  in
                      let uu____17080 = FStar_Ident.string_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17078 uu____17080
                       in
                    failwith uu____17076
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17083;
                      FStar_TypeChecker_Env.mtarget = uu____17084;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17085;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17105 =
                      let uu____17107 = FStar_Ident.string_of_lid msrc  in
                      let uu____17109 = FStar_Ident.string_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17107 uu____17109
                       in
                    failwith uu____17105
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17112;
                      FStar_TypeChecker_Env.mtarget = uu____17113;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17114;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____17145 =
                        FStar_TypeChecker_Env.is_reifiable_effect env1 msrc
                         in
                      if uu____17145
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____17150 =
                           let uu____17151 =
                             let uu____17170 =
                               let uu____17179 =
                                 FStar_Syntax_Syntax.null_binder
                                   FStar_Syntax_Syntax.t_unit
                                  in
                               [uu____17179]  in
                             (uu____17170, e,
                               (FStar_Pervasives_Native.Some
                                  {
                                    FStar_Syntax_Syntax.residual_effect =
                                      msrc;
                                    FStar_Syntax_Syntax.residual_typ =
                                      (FStar_Pervasives_Native.Some t);
                                    FStar_Syntax_Syntax.residual_flags = []
                                  }))
                              in
                           FStar_Syntax_Syntax.Tm_abs uu____17151  in
                         FStar_Syntax_Syntax.mk uu____17150
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____17212 =
                      env1.FStar_TypeChecker_Env.universe_of env1 t  in
                    lift uu____17212 t e1))

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
                (fun uu____17282  ->
                   match uu____17282 with
                   | (a,imp) ->
                       let uu____17301 = norm cfg env1 [] a  in
                       (uu____17301, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env1  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17311  ->
             let uu____17312 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17314 =
               FStar_Util.string_of_int (FStar_List.length env1)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17312 uu____17314);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env1 [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17340 = norm_universe cfg env1 u  in
                   FStar_All.pipe_left
                     (fun uu____17343  ->
                        FStar_Pervasives_Native.Some uu____17343) uu____17340
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2109_17344 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2109_17344.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2109_17344.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env1 [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17366 = norm_universe cfg env1 u  in
                   FStar_All.pipe_left
                     (fun uu____17369  ->
                        FStar_Pervasives_Native.Some uu____17369) uu____17366
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2120_17370 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2120_17370.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2120_17370.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17415  ->
                      match uu____17415 with
                      | (a,i) ->
                          let uu____17435 = norm cfg env1 [] a  in
                          (uu____17435, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17457  ->
                       match uu___14_17457 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17461 = norm cfg env1 [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17461
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env1)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env1 [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2137_17469 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2139_17472 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2139_17472.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2137_17469.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2137_17469.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env1  ->
      fun b  ->
        let uu____17476 = b  in
        match uu____17476 with
        | (x,imp) ->
            let x1 =
              let uu___2147_17484 = x  in
              let uu____17485 = norm cfg env1 [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2147_17484.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2147_17484.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17485
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____17496 =
                    let uu____17497 = closure_as_term cfg env1 t  in
                    FStar_Syntax_Syntax.Meta uu____17497  in
                  FStar_Pervasives_Native.Some uu____17496
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env1  ->
      fun bs  ->
        let uu____17508 =
          FStar_List.fold_left
            (fun uu____17542  ->
               fun b  ->
                 match uu____17542 with
                 | (nbs',env2) ->
                     let b1 = norm_binder cfg env2 b  in
                     ((b1 :: nbs'), (dummy :: env2))) ([], env1) bs
           in
        match uu____17508 with | (nbs,uu____17622) -> FStar_List.rev nbs

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
            let uu____17654 =
              let uu___2172_17655 = rc  in
              let uu____17656 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env1 [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2172_17655.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17656;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2172_17655.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17654
        | uu____17674 -> lopt

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
            (let uu____17684 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17686 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17684 uu____17686)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_17698  ->
      match uu___15_17698 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17711 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17711 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17715 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____17715)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun tm  ->
          let tm1 =
            let uu____17723 = norm_cb cfg  in
            reduce_primops uu____17723 cfg env1 tm  in
          let uu____17728 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17728
          then tm1
          else
            (let w t =
               let uu___2201_17747 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2201_17747.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2201_17747.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17759 =
                 let uu____17760 = FStar_Syntax_Util.unmeta t  in
                 uu____17760.FStar_Syntax_Syntax.n  in
               match uu____17759 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17772 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17836)::args1,(bv,uu____17839)::bs1) ->
                   let uu____17893 =
                     let uu____17894 = FStar_Syntax_Subst.compress t  in
                     uu____17894.FStar_Syntax_Syntax.n  in
                   (match uu____17893 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17899 -> false)
               | ([],[]) -> true
               | (uu____17930,uu____17931) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17982 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17984 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17982
                    uu____17984)
               else ();
               (let uu____17989 = FStar_Syntax_Util.head_and_args' t  in
                match uu____17989 with
                | (hd,args) ->
                    let uu____18028 =
                      let uu____18029 = FStar_Syntax_Subst.compress hd  in
                      uu____18029.FStar_Syntax_Syntax.n  in
                    (match uu____18028 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____18037 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18039 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18041 =
                               FStar_Syntax_Print.term_to_string hd  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18037 uu____18039 uu____18041)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18046 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18064 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18066 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18064
                    uu____18066)
               else ();
               (let uu____18071 = FStar_Syntax_Util.is_squash t  in
                match uu____18071 with
                | FStar_Pervasives_Native.Some (uu____18082,t') ->
                    is_applied bs t'
                | uu____18094 ->
                    let uu____18103 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18103 with
                     | FStar_Pervasives_Native.Some (uu____18114,t') ->
                         is_applied bs t'
                     | uu____18126 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18150 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18150 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18157)::(q,uu____18159)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18202 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18204 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18202 uu____18204)
                    else ();
                    (let uu____18209 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18209 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18214 =
                           let uu____18215 = FStar_Syntax_Subst.compress p
                              in
                           uu____18215.FStar_Syntax_Syntax.n  in
                         (match uu____18214 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18226 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18226))
                          | uu____18229 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18232)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18257 =
                           let uu____18258 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18258.FStar_Syntax_Syntax.n  in
                         (match uu____18257 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18269 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18269))
                          | uu____18272 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18276 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18276 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18281 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18281 with
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
                                     let uu____18295 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18295))
                               | uu____18298 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18303)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18328 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18328 with
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
                                     let uu____18342 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18342))
                               | uu____18345 -> FStar_Pervasives_Native.None)
                          | uu____18348 -> FStar_Pervasives_Native.None)
                     | uu____18351 -> FStar_Pervasives_Native.None))
               | uu____18354 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18367 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18367 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18373)::[],uu____18374,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18394 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18396 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18394
                         uu____18396)
                    else ();
                    is_quantified_const bv phi')
               | uu____18401 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18416 =
                 let uu____18417 = FStar_Syntax_Subst.compress phi  in
                 uu____18417.FStar_Syntax_Syntax.n  in
               match uu____18416 with
               | FStar_Syntax_Syntax.Tm_match (uu____18423,br::brs) ->
                   let uu____18490 = br  in
                   (match uu____18490 with
                    | (uu____18508,uu____18509,e) ->
                        let r =
                          let uu____18531 = simp_t e  in
                          match uu____18531 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18543 =
                                FStar_List.for_all
                                  (fun uu____18562  ->
                                     match uu____18562 with
                                     | (uu____18576,uu____18577,e') ->
                                         let uu____18591 = simp_t e'  in
                                         uu____18591 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18543
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18607 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18617 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18617
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18653 =
                 match uu____18653 with
                 | (t1,q) ->
                     let uu____18674 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18674 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18706 -> (t1, q))
                  in
               let uu____18719 = FStar_Syntax_Util.head_and_args t  in
               match uu____18719 with
               | (head,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head args1
                     t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18797 =
                 let uu____18798 = FStar_Syntax_Util.unmeta ty  in
                 uu____18798.FStar_Syntax_Syntax.n  in
               match uu____18797 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18803) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18808,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18832 -> false  in
             let simplify arg =
               let uu____18865 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18865, arg)  in
             let uu____18880 = is_forall_const tm1  in
             match uu____18880 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____18886 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18888 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18886
                       uu____18888)
                  else ();
                  (let uu____18893 = norm cfg env1 [] tm'  in
                   maybe_simplify_aux cfg env1 stack1 uu____18893))
             | FStar_Pervasives_Native.None  ->
                 let uu____18894 =
                   let uu____18895 = FStar_Syntax_Subst.compress tm1  in
                   uu____18895.FStar_Syntax_Syntax.n  in
                 (match uu____18894 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18899;
                              FStar_Syntax_Syntax.vars = uu____18900;_},uu____18901);
                         FStar_Syntax_Syntax.pos = uu____18902;
                         FStar_Syntax_Syntax.vars = uu____18903;_},args)
                      ->
                      let uu____18933 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18933
                      then
                        let uu____18936 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        (match uu____18936 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18994)::
                             (uu____18995,(arg,uu____18997))::[] ->
                             maybe_auto_squash arg
                         | (uu____19070,(arg,uu____19072))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19073)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19146)::uu____19147::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19217::(FStar_Pervasives_Native.Some (false
                                         ),uu____19218)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19288 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19306 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19306
                         then
                           let uu____19309 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify)
                              in
                           match uu____19309 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19367)::uu____19368::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19438::(FStar_Pervasives_Native.Some (true
                                           ),uu____19439)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19509)::(uu____19510,(arg,uu____19512))::[]
                               -> maybe_auto_squash arg
                           | (uu____19585,(arg,uu____19587))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19588)::[]
                               -> maybe_auto_squash arg
                           | uu____19661 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19679 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19679
                            then
                              let uu____19682 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify)
                                 in
                              match uu____19682 with
                              | uu____19740::(FStar_Pervasives_Native.Some
                                              (true ),uu____19741)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19811)::uu____19812::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19882)::(uu____19883,(arg,uu____19885))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19958,(p,uu____19960))::(uu____19961,
                                                                (q,uu____19963))::[]
                                  ->
                                  let uu____20035 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20035
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20040 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20058 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20058
                               then
                                 let uu____20061 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify)
                                    in
                                 match uu____20061 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20119)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20120)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20194)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20195)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20269)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20270)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20344)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20345)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20419,(arg,uu____20421))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20422)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20495)::(uu____20496,(arg,uu____20498))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20571,(arg,uu____20573))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20574)::[]
                                     ->
                                     let uu____20647 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20647
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20648)::(uu____20649,(arg,uu____20651))::[]
                                     ->
                                     let uu____20724 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20724
                                 | (uu____20725,(p,uu____20727))::(uu____20728,
                                                                   (q,uu____20730))::[]
                                     ->
                                     let uu____20802 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20802
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20807 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20825 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20825
                                  then
                                    let uu____20828 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify)
                                       in
                                    match uu____20828 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20886)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20930)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20974 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20992 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20992
                                     then
                                       match args with
                                       | (t,uu____20996)::[] ->
                                           let uu____21021 =
                                             let uu____21022 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21022.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21021 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21025::[],body,uu____21027)
                                                ->
                                                let uu____21062 = simp_t body
                                                   in
                                                (match uu____21062 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21068 -> tm1)
                                            | uu____21072 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21074))::(t,uu____21076)::[]
                                           ->
                                           let uu____21116 =
                                             let uu____21117 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21117.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21116 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21120::[],body,uu____21122)
                                                ->
                                                let uu____21157 = simp_t body
                                                   in
                                                (match uu____21157 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21165 -> tm1)
                                            | uu____21169 -> tm1)
                                       | uu____21170 -> tm1
                                     else
                                       (let uu____21183 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21183
                                        then
                                          match args with
                                          | (t,uu____21187)::[] ->
                                              let uu____21212 =
                                                let uu____21213 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21213.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21212 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21216::[],body,uu____21218)
                                                   ->
                                                   let uu____21253 =
                                                     simp_t body  in
                                                   (match uu____21253 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21259 -> tm1)
                                               | uu____21263 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21265))::(t,uu____21267)::[]
                                              ->
                                              let uu____21307 =
                                                let uu____21308 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21308.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21307 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21311::[],body,uu____21313)
                                                   ->
                                                   let uu____21348 =
                                                     simp_t body  in
                                                   (match uu____21348 with
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
                                                    | uu____21356 -> tm1)
                                               | uu____21360 -> tm1)
                                          | uu____21361 -> tm1
                                        else
                                          (let uu____21374 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21374
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21377;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21378;_},uu____21379)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21405;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21406;_},uu____21407)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21433 -> tm1
                                           else
                                             (let uu____21446 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____21446
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____21460 =
                                                    let uu____21461 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____21461.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____21460 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21472 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21486 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____21486
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____21525 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____21525
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21531 =
                                                         let uu____21532 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____21532.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____21531 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21535 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____21543 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____21543
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21552
                                                                  =
                                                                  let uu____21553
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____21553.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____21552
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,uu____21559)
                                                                    -> hd
                                                                | uu____21584
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____21588
                                                                =
                                                                let uu____21599
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____21599]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21588)
                                                       | uu____21632 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21637 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____21637 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21657 ->
                                                     let uu____21666 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____21666 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21672;
                         FStar_Syntax_Syntax.vars = uu____21673;_},args)
                      ->
                      let uu____21699 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21699
                      then
                        let uu____21702 =
                          FStar_All.pipe_right args (FStar_List.map simplify)
                           in
                        (match uu____21702 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21760)::
                             (uu____21761,(arg,uu____21763))::[] ->
                             maybe_auto_squash arg
                         | (uu____21836,(arg,uu____21838))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21839)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21912)::uu____21913::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21983::(FStar_Pervasives_Native.Some (false
                                         ),uu____21984)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22054 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22072 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22072
                         then
                           let uu____22075 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify)
                              in
                           match uu____22075 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22133)::uu____22134::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22204::(FStar_Pervasives_Native.Some (true
                                           ),uu____22205)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22275)::(uu____22276,(arg,uu____22278))::[]
                               -> maybe_auto_squash arg
                           | (uu____22351,(arg,uu____22353))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22354)::[]
                               -> maybe_auto_squash arg
                           | uu____22427 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22445 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22445
                            then
                              let uu____22448 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify)
                                 in
                              match uu____22448 with
                              | uu____22506::(FStar_Pervasives_Native.Some
                                              (true ),uu____22507)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22577)::uu____22578::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22648)::(uu____22649,(arg,uu____22651))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22724,(p,uu____22726))::(uu____22727,
                                                                (q,uu____22729))::[]
                                  ->
                                  let uu____22801 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22801
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22806 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22824 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22824
                               then
                                 let uu____22827 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify)
                                    in
                                 match uu____22827 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22885)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22886)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22960)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22961)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23035)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23036)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23110)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23111)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23185,(arg,uu____23187))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23188)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23261)::(uu____23262,(arg,uu____23264))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23337,(arg,uu____23339))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23340)::[]
                                     ->
                                     let uu____23413 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23413
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23414)::(uu____23415,(arg,uu____23417))::[]
                                     ->
                                     let uu____23490 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23490
                                 | (uu____23491,(p,uu____23493))::(uu____23494,
                                                                   (q,uu____23496))::[]
                                     ->
                                     let uu____23568 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23568
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23573 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23591 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23591
                                  then
                                    let uu____23594 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify)
                                       in
                                    match uu____23594 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23652)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23696)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23740 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23758 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23758
                                     then
                                       match args with
                                       | (t,uu____23762)::[] ->
                                           let uu____23787 =
                                             let uu____23788 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23788.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23787 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23791::[],body,uu____23793)
                                                ->
                                                let uu____23828 = simp_t body
                                                   in
                                                (match uu____23828 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23834 -> tm1)
                                            | uu____23838 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23840))::(t,uu____23842)::[]
                                           ->
                                           let uu____23882 =
                                             let uu____23883 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23883.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23882 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23886::[],body,uu____23888)
                                                ->
                                                let uu____23923 = simp_t body
                                                   in
                                                (match uu____23923 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____23931 -> tm1)
                                            | uu____23935 -> tm1)
                                       | uu____23936 -> tm1
                                     else
                                       (let uu____23949 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____23949
                                        then
                                          match args with
                                          | (t,uu____23953)::[] ->
                                              let uu____23978 =
                                                let uu____23979 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23979.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23978 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23982::[],body,uu____23984)
                                                   ->
                                                   let uu____24019 =
                                                     simp_t body  in
                                                   (match uu____24019 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24025 -> tm1)
                                               | uu____24029 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24031))::(t,uu____24033)::[]
                                              ->
                                              let uu____24073 =
                                                let uu____24074 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24074.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24073 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24077::[],body,uu____24079)
                                                   ->
                                                   let uu____24114 =
                                                     simp_t body  in
                                                   (match uu____24114 with
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
                                                    | uu____24122 -> tm1)
                                               | uu____24126 -> tm1)
                                          | uu____24127 -> tm1
                                        else
                                          (let uu____24140 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24140
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24143;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24144;_},uu____24145)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24171;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24172;_},uu____24173)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24199 -> tm1
                                           else
                                             (let uu____24212 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____24212
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____24226 =
                                                    let uu____24227 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____24227.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____24226 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____24238 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24252 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____24252
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____24287 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____24287
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24293 =
                                                         let uu____24294 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____24294.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____24293 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24297 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24305 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24305
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24314
                                                                  =
                                                                  let uu____24315
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24315.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24314
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd,uu____24321)
                                                                    -> hd
                                                                | uu____24346
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____24350
                                                                =
                                                                let uu____24361
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____24361]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24350)
                                                       | uu____24394 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24399 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____24399 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24419 ->
                                                     let uu____24428 =
                                                       norm_cb cfg  in
                                                     reduce_equality
                                                       uu____24428 cfg env1
                                                       tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24439 = simp_t t  in
                      (match uu____24439 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24448 ->
                      let uu____24471 = is_const_match tm1  in
                      (match uu____24471 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24480 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env1  ->
      fun stack1  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____24490  ->
               (let uu____24492 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24494 = FStar_Syntax_Print.term_to_string t  in
                let uu____24496 =
                  FStar_Util.string_of_int (FStar_List.length env1)  in
                let uu____24504 =
                  let uu____24506 =
                    let uu____24509 = firstn (Prims.of_int (4)) stack1  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24509
                     in
                  stack_to_string uu____24506  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24492 uu____24494 uu____24496 uu____24504);
               (let uu____24534 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24534
                then
                  let uu____24538 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24538 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24545 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24547 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24549 =
                          let uu____24551 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24551
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24545
                          uu____24547 uu____24549);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____24573 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack1 with
                | (Arg uu____24581)::uu____24582 -> true
                | uu____24592 -> false)
              in
           if uu____24573
           then
             let uu____24595 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____24595 (norm cfg env1 stack1)
           else
             (let t1 = maybe_simplify cfg env1 stack1 t  in
              match stack1 with
              | [] -> t1
              | (Debug (tm,time_then))::stack2 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____24609 =
                        let uu____24611 =
                          let uu____24613 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____24613  in
                        FStar_Util.string_of_int uu____24611  in
                      let uu____24620 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____24622 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                      let uu____24624 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____24609 uu____24620 uu____24622 uu____24624)
                   else ();
                   rebuild cfg env1 stack2 t1)
              | (Cfg cfg1)::stack2 -> rebuild cfg1 env1 stack2 t1
              | (Meta (uu____24633,m,r))::stack2 ->
                  let t2 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_meta (t1, m)) r
                     in
                  rebuild cfg env1 stack2 t2
              | (MemoLazy r)::stack2 ->
                  (set_memo cfg r (env1, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24662  ->
                        let uu____24663 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24663);
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
                  let uu____24706 =
                    let uu___2830_24707 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2830_24707.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2830_24707.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env1 stack2 uu____24706
              | (Arg (Univ uu____24710,uu____24711,uu____24712))::uu____24713
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____24717,uu____24718))::uu____24719 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env1 stack2 t2
              | (Arg
                  (Clos (env_arg,tm,uu____24735,uu____24736),aq,r))::stack2
                  when
                  let uu____24788 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24788 ->
                  let t2 =
                    let uu____24790 =
                      let uu____24791 = closure_as_term cfg env_arg tm  in
                      (uu____24791, aq)  in
                    FStar_Syntax_Syntax.extend_app t1 uu____24790 r  in
                  rebuild cfg env1 stack2 t2
              | (Arg (Clos (env_arg,tm,m,uu____24801),aq,r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24856  ->
                        let uu____24857 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____24857);
                   if
                     Prims.op_Negation
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                   then
                     (if
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                      then
                        let arg = closure_as_term cfg env_arg tm  in
                        let t2 =
                          FStar_Syntax_Syntax.extend_app t1 (arg, aq) r  in
                        rebuild cfg env_arg stack2 t2
                      else
                        (let stack3 = (App (env1, t1, aq, r)) :: stack2  in
                         norm cfg env_arg stack3 tm))
                   else
                     (let uu____24875 = FStar_ST.op_Bang m  in
                      match uu____24875 with
                      | FStar_Pervasives_Native.None  ->
                          if
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
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
                      | FStar_Pervasives_Native.Some (uu____24961,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq) r  in
                          rebuild cfg env_arg stack2 t2))
              | (App (env2,head,aq,r))::stack' when should_reify cfg stack1
                  ->
                  let t0 = t1  in
                  let fallback msg uu____25015 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____25020  ->
                         let uu____25021 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____25021);
                    (let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r
                        in
                     rebuild cfg env2 stack' t2)
                     in
                  let uu____25029 =
                    let uu____25030 = FStar_Syntax_Subst.compress t1  in
                    uu____25030.FStar_Syntax_Syntax.n  in
                  (match uu____25029 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env2 stack1 t2
                         m ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____25058 = closure_as_term cfg env2 ty  in
                         reify_lift cfg t2 msrc mtgt uu____25058  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____25062  ->
                             let uu____25063 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____25063);
                        (let uu____25066 = FStar_List.tl stack1  in
                         norm cfg env2 uu____25066 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____25067);
                          FStar_Syntax_Syntax.pos = uu____25068;
                          FStar_Syntax_Syntax.vars = uu____25069;_},(e,uu____25071)::[])
                       -> norm cfg env2 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____25110 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____25127 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____25127 with
                        | (hd,args) ->
                            let uu____25170 =
                              let uu____25171 = FStar_Syntax_Util.un_uinst hd
                                 in
                              uu____25171.FStar_Syntax_Syntax.n  in
                            (match uu____25170 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____25175 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____25175 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____25178;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____25179;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____25180;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____25182;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____25183;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____25184;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____25185;_}
                                      when (FStar_List.length args) = n ->
                                      norm cfg env2 stack' t1
                                  | uu____25221 -> fallback " (3)" ())
                             | uu____25225 -> fallback " (4)" ()))
                   | uu____25227 -> fallback " (2)" ())
              | (App (env2,head,aq,r))::stack2 ->
                  let t2 = FStar_Syntax_Syntax.extend_app head (t1, aq) r  in
                  rebuild cfg env2 stack2 t2
              | (CBVApp (env',head,aq,r))::stack2 ->
                  let uu____25248 =
                    let uu____25249 =
                      let uu____25250 =
                        let uu____25257 =
                          let uu____25258 =
                            let uu____25290 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env1, t1, uu____25290, false)  in
                          Clos uu____25258  in
                        (uu____25257, aq, (t1.FStar_Syntax_Syntax.pos))  in
                      Arg uu____25250  in
                    uu____25249 :: stack2  in
                  norm cfg env' uu____25248 head
              | (Match (env',branches1,cfg1,r))::stack2 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____25365  ->
                        let uu____25366 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____25366);
                   (let scrutinee_env = env1  in
                    let env2 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____25377 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25382  ->
                           let uu____25383 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____25385 =
                             let uu____25387 =
                               FStar_All.pipe_right branches1
                                 (FStar_List.map
                                    (fun uu____25417  ->
                                       match uu____25417 with
                                       | (p,uu____25428,uu____25429) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____25387
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____25383 uu____25385);
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
                                   (fun uu___16_25454  ->
                                      match uu___16_25454 with
                                      | FStar_TypeChecker_Env.InliningDelta 
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                           -> true
                                      | uu____25458 -> false))
                               in
                            let steps =
                              let uu___3007_25461 =
                                cfg1.FStar_TypeChecker_Cfg.steps  in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.zeta_full =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.zeta_full);
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3007_25461.FStar_TypeChecker_Cfg.for_extraction)
                              }  in
                            let uu___3010_25468 = cfg1  in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3010_25468.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3010_25468.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3010_25468.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3010_25468.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3010_25468.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3010_25468.FStar_TypeChecker_Cfg.reifying)
                            })
                          in
                       let norm_or_whnf env3 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env3 t2
                         else norm cfg_exclude_zeta env3 [] t2  in
                       let rec norm_pat env3 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____25543 ->
                             (p, env3)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____25574 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25663  ->
                                       fun uu____25664  ->
                                         match (uu____25663, uu____25664)
                                         with
                                         | ((pats1,env4),(p1,b)) ->
                                             let uu____25814 =
                                               norm_pat env4 p1  in
                                             (match uu____25814 with
                                              | (p2,env5) ->
                                                  (((p2, b) :: pats1), env5)))
                                    ([], env3))
                                in
                             (match uu____25574 with
                              | (pats1,env4) ->
                                  ((let uu___3038_25984 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3038_25984.FStar_Syntax_Syntax.p)
                                    }), env4))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3042_26005 = x  in
                               let uu____26006 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3042_26005.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3042_26005.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26006
                               }  in
                             ((let uu___3045_26020 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3045_26020.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3049_26031 = x  in
                               let uu____26032 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3049_26031.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3049_26031.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26032
                               }  in
                             ((let uu___3052_26046 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3052_26046.FStar_Syntax_Syntax.p)
                               }), (dummy :: env3))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3058_26062 = x  in
                               let uu____26063 =
                                 norm_or_whnf env3 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3058_26062.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3058_26062.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26063
                               }  in
                             let t3 = norm_or_whnf env3 t2  in
                             ((let uu___3062_26078 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3062_26078.FStar_Syntax_Syntax.p)
                               }), env3)
                          in
                       let branches2 =
                         match env2 with
                         | [] when whnf -> branches1
                         | uu____26122 ->
                             FStar_All.pipe_right branches1
                               (FStar_List.map
                                  (fun branch  ->
                                     let uu____26152 =
                                       FStar_Syntax_Subst.open_branch branch
                                        in
                                     match uu____26152 with
                                     | (p,wopt,e) ->
                                         let uu____26172 = norm_pat env2 p
                                            in
                                         (match uu____26172 with
                                          | (p1,env3) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____26227 =
                                                      norm_or_whnf env3 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____26227
                                                 in
                                              let e1 = norm_or_whnf env3 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____26244 =
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
                         if uu____26244
                         then
                           norm
                             (let uu___3081_26251 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3083_26254 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.zeta_full =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.zeta_full);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3083_26254.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3081_26251.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3081_26251.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3081_26251.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3081_26251.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3081_26251.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3081_26251.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3081_26251.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3081_26251.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____26258 =
                         FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches2)) r
                          in
                       rebuild cfg1 env2 stack2 uu____26258)
                       in
                    let rec is_cons head =
                      let uu____26284 =
                        let uu____26285 = FStar_Syntax_Subst.compress head
                           in
                        uu____26285.FStar_Syntax_Syntax.n  in
                      match uu____26284 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____26290) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____26295 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26297;
                            FStar_Syntax_Syntax.fv_delta = uu____26298;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26300;
                            FStar_Syntax_Syntax.fv_delta = uu____26301;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____26302);_}
                          -> true
                      | uu____26310 -> false  in
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
                      let uu____26479 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____26479 with
                      | (head,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____26576 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26618 ->
                                    let uu____26619 =
                                      let uu____26621 = is_cons head  in
                                      Prims.op_Negation uu____26621  in
                                    FStar_Util.Inr uu____26619)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____26650 =
                                 let uu____26651 =
                                   FStar_Syntax_Util.un_uinst head  in
                                 uu____26651.FStar_Syntax_Syntax.n  in
                               (match uu____26650 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26670 ->
                                    let uu____26671 =
                                      let uu____26673 = is_cons head  in
                                      Prims.op_Negation uu____26673  in
                                    FStar_Util.Inr uu____26671))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____26764)::rest_a,(p1,uu____26767)::rest_p)
                          ->
                          let uu____26826 = matches_pat t2 p1  in
                          (match uu____26826 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____26879 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____27002 = matches_pat scrutinee1 p1  in
                          (match uu____27002 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____27048  ->
                                     let uu____27049 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____27051 =
                                       let uu____27053 =
                                         FStar_List.map
                                           (fun uu____27065  ->
                                              match uu____27065 with
                                              | (uu____27071,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____27053
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____27049 uu____27051);
                                (let env0 = env2  in
                                 let env3 =
                                   FStar_List.fold_left
                                     (fun env3  ->
                                        fun uu____27107  ->
                                          match uu____27107 with
                                          | (bv,t2) ->
                                              let uu____27130 =
                                                let uu____27137 =
                                                  let uu____27140 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____27140
                                                   in
                                                let uu____27141 =
                                                  let uu____27142 =
                                                    let uu____27174 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____27174,
                                                      false)
                                                     in
                                                  Clos uu____27142  in
                                                (uu____27137, uu____27141)
                                                 in
                                              uu____27130 :: env3) env2 s
                                    in
                                 let uu____27267 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env3 stack2 uu____27267)))
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
            (fun uu____27300  ->
               let uu____27301 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____27301);
          (let uu____27304 = is_nbe_request s  in
           if uu____27304
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27310  ->
                   let uu____27311 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27311);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27317  ->
                   let uu____27318 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27318);
              (let uu____27321 =
                 FStar_Util.record_time (fun uu____27328  -> nbe_eval c s t)
                  in
               match uu____27321 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27337  ->
                         let uu____27338 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27340 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27338 uu____27340);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27348  ->
                   let uu____27349 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27349);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27355  ->
                   let uu____27356 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27356);
              (let uu____27359 =
                 FStar_Util.record_time (fun uu____27366  -> norm c [] [] t)
                  in
               match uu____27359 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27381  ->
                         let uu____27382 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27384 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27382 uu____27384);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27403 =
          let uu____27407 =
            let uu____27409 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____27409  in
          FStar_Pervasives_Native.Some uu____27407  in
        FStar_Profiling.profile
          (fun uu____27412  -> normalize_with_primitive_steps [] s e t)
          uu____27403 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____27434  ->
             let uu____27435 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27435);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27441  ->
             let uu____27442 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27442);
        (let uu____27445 =
           FStar_Util.record_time (fun uu____27452  -> norm_comp cfg [] c)
            in
         match uu____27445 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27467  ->
                   let uu____27468 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____27470 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27468
                     uu____27470);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env1  ->
    fun u  ->
      let uu____27484 = FStar_TypeChecker_Cfg.config [] env1  in
      norm_universe uu____27484 [] u
  
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
      let uu____27506 = normalize steps env1 t  in
      FStar_TypeChecker_Env.non_informative env1 uu____27506
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env1  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27518 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env1 t ->
          let uu___3251_27537 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3251_27537.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3251_27537.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env1
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27544 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env1 ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27544
          then
            let ct1 =
              let uu____27548 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27548 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____27555 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27555
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3261_27562 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3261_27562.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3261_27562.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3261_27562.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env1 c
                     in
                  let uu___3265_27564 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3265_27564.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3265_27564.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3265_27564.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3265_27564.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3268_27565 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3268_27565.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3268_27565.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27568 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env1  ->
    fun lc  ->
      let uu____27580 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env1 lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____27580
      then
        let uu____27583 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____27583 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3276_27587 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env1)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3276_27587.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3276_27587.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3276_27587.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env1  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3283_27606  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                   t) ()
        with
        | uu___3282_27609 ->
            ((let uu____27611 =
                let uu____27617 =
                  let uu____27619 = FStar_Util.message_of_exn uu___3282_27609
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27619
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27617)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27611);
             t)
         in
      FStar_Syntax_Print.term_to_string' env1.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env1  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3293_27638  ->
             match () with
             | () ->
                 let uu____27639 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env1
                    in
                 norm_comp uu____27639 [] c) ()
        with
        | uu___3292_27648 ->
            ((let uu____27650 =
                let uu____27656 =
                  let uu____27658 = FStar_Util.message_of_exn uu___3292_27648
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27658
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27656)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27650);
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
                   let uu____27707 =
                     let uu____27708 =
                       let uu____27715 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27715)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27708  in
                   FStar_Syntax_Syntax.mk uu____27707
                     t01.FStar_Syntax_Syntax.pos
               | uu____27720 -> t2)
          | uu____27721 -> t2  in
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
        let uu____27815 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27815 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27828 ->
                 let uu____27829 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27829 with
                  | (actuals,uu____27839,uu____27840) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27860 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27860 with
                         | (binders,args) ->
                             let uu____27871 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27871
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
      | uu____27886 ->
          let uu____27887 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27887 with
           | (head,args) ->
               let uu____27930 =
                 let uu____27931 = FStar_Syntax_Subst.compress head  in
                 uu____27931.FStar_Syntax_Syntax.n  in
               (match uu____27930 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____27952 =
                      let uu____27959 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____27959  in
                    (match uu____27952 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27983 =
                              env1.FStar_TypeChecker_Env.type_of
                                (let uu___3363_27991 = env1  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3363_27991.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3363_27991.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3363_27991.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3363_27991.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3363_27991.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3363_27991.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3363_27991.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3363_27991.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3363_27991.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3363_27991.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3363_27991.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3363_27991.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3363_27991.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3363_27991.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3363_27991.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3363_27991.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3363_27991.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3363_27991.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3363_27991.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3363_27991.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3363_27991.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3363_27991.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3363_27991.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3363_27991.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3363_27991.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3363_27991.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3363_27991.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3363_27991.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3363_27991.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3363_27991.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3363_27991.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3363_27991.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3363_27991.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3363_27991.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3363_27991.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3363_27991.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3363_27991.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3363_27991.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3363_27991.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3363_27991.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3363_27991.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3363_27991.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3363_27991.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____27983 with
                            | (uu____27994,ty,uu____27996) ->
                                eta_expand_with_type env1 t ty))
                | uu____27997 ->
                    let uu____27998 =
                      env1.FStar_TypeChecker_Env.type_of
                        (let uu___3370_28006 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3370_28006.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3370_28006.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3370_28006.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3370_28006.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3370_28006.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3370_28006.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3370_28006.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3370_28006.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3370_28006.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3370_28006.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3370_28006.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3370_28006.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3370_28006.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3370_28006.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3370_28006.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3370_28006.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3370_28006.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3370_28006.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3370_28006.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3370_28006.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3370_28006.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3370_28006.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3370_28006.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3370_28006.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3370_28006.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3370_28006.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3370_28006.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3370_28006.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3370_28006.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3370_28006.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3370_28006.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3370_28006.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3370_28006.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3370_28006.FStar_TypeChecker_Env.try_solve_implicits_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3370_28006.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3370_28006.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3370_28006.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3370_28006.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3370_28006.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3370_28006.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3370_28006.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3370_28006.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3370_28006.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____27998 with
                     | (uu____28009,ty,uu____28011) ->
                         eta_expand_with_type env1 t ty)))
  
let rec (elim_delayed_subst_term :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos  in
    let t1 = FStar_Syntax_Subst.compress t  in
    let elim_bv x =
      let uu___3382_28093 = x  in
      let uu____28094 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3382_28093.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3382_28093.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28094
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28097 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28113 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28114 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28115 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28116 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28123 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28124 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28125 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3408_28159 = rc  in
          let uu____28160 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28169 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3408_28159.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28160;
            FStar_Syntax_Syntax.residual_flags = uu____28169
          }  in
        let uu____28172 =
          let uu____28173 =
            let uu____28192 = elim_delayed_subst_binders bs  in
            let uu____28201 = elim_delayed_subst_term t2  in
            let uu____28204 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28192, uu____28201, uu____28204)  in
          FStar_Syntax_Syntax.Tm_abs uu____28173  in
        mk uu____28172
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28241 =
          let uu____28242 =
            let uu____28257 = elim_delayed_subst_binders bs  in
            let uu____28266 = elim_delayed_subst_comp c  in
            (uu____28257, uu____28266)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28242  in
        mk uu____28241
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28285 =
          let uu____28286 =
            let uu____28293 = elim_bv bv  in
            let uu____28294 = elim_delayed_subst_term phi  in
            (uu____28293, uu____28294)  in
          FStar_Syntax_Syntax.Tm_refine uu____28286  in
        mk uu____28285
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28325 =
          let uu____28326 =
            let uu____28343 = elim_delayed_subst_term t2  in
            let uu____28346 = elim_delayed_subst_args args  in
            (uu____28343, uu____28346)  in
          FStar_Syntax_Syntax.Tm_app uu____28326  in
        mk uu____28325
    | FStar_Syntax_Syntax.Tm_match (t2,branches1) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3430_28418 = p  in
              let uu____28419 =
                let uu____28420 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28420  in
              {
                FStar_Syntax_Syntax.v = uu____28419;
                FStar_Syntax_Syntax.p =
                  (uu___3430_28418.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3434_28422 = p  in
              let uu____28423 =
                let uu____28424 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28424  in
              {
                FStar_Syntax_Syntax.v = uu____28423;
                FStar_Syntax_Syntax.p =
                  (uu___3434_28422.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3440_28431 = p  in
              let uu____28432 =
                let uu____28433 =
                  let uu____28440 = elim_bv x  in
                  let uu____28441 = elim_delayed_subst_term t0  in
                  (uu____28440, uu____28441)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28433  in
              {
                FStar_Syntax_Syntax.v = uu____28432;
                FStar_Syntax_Syntax.p =
                  (uu___3440_28431.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3446_28466 = p  in
              let uu____28467 =
                let uu____28468 =
                  let uu____28482 =
                    FStar_List.map
                      (fun uu____28508  ->
                         match uu____28508 with
                         | (x,b) ->
                             let uu____28525 = elim_pat x  in
                             (uu____28525, b)) pats
                     in
                  (fv, uu____28482)  in
                FStar_Syntax_Syntax.Pat_cons uu____28468  in
              {
                FStar_Syntax_Syntax.v = uu____28467;
                FStar_Syntax_Syntax.p =
                  (uu___3446_28466.FStar_Syntax_Syntax.p)
              }
          | uu____28540 -> p  in
        let elim_branch uu____28564 =
          match uu____28564 with
          | (pat,wopt,t3) ->
              let uu____28590 = elim_pat pat  in
              let uu____28593 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28596 = elim_delayed_subst_term t3  in
              (uu____28590, uu____28593, uu____28596)
           in
        let uu____28601 =
          let uu____28602 =
            let uu____28625 = elim_delayed_subst_term t2  in
            let uu____28628 = FStar_List.map elim_branch branches1  in
            (uu____28625, uu____28628)  in
          FStar_Syntax_Syntax.Tm_match uu____28602  in
        mk uu____28601
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28759 =
          match uu____28759 with
          | (tc,topt) ->
              let uu____28794 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28804 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28804
                | FStar_Util.Inr c ->
                    let uu____28806 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28806
                 in
              let uu____28807 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28794, uu____28807)
           in
        let uu____28816 =
          let uu____28817 =
            let uu____28844 = elim_delayed_subst_term t2  in
            let uu____28847 = elim_ascription a  in
            (uu____28844, uu____28847, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28817  in
        mk uu____28816
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3476_28910 = lb  in
          let uu____28911 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____28914 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3476_28910.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3476_28910.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28911;
            FStar_Syntax_Syntax.lbeff =
              (uu___3476_28910.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28914;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3476_28910.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3476_28910.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____28917 =
          let uu____28918 =
            let uu____28932 =
              let uu____28940 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____28940)  in
            let uu____28952 = elim_delayed_subst_term t2  in
            (uu____28932, uu____28952)  in
          FStar_Syntax_Syntax.Tm_let uu____28918  in
        mk uu____28917
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____28997 =
          let uu____28998 =
            let uu____29005 = elim_delayed_subst_term tm  in
            (uu____29005, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____28998  in
        mk uu____28997
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29016 =
          let uu____29017 =
            let uu____29024 = elim_delayed_subst_term t2  in
            let uu____29027 = elim_delayed_subst_meta md  in
            (uu____29024, uu____29027)  in
          FStar_Syntax_Syntax.Tm_meta uu____29017  in
        mk uu____29016

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29036  ->
         match uu___17_29036 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29040 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29040
         | f -> f) flags

and (elim_delayed_subst_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp) =
  fun c  ->
    let mk x = FStar_Syntax_Syntax.mk x c.FStar_Syntax_Syntax.pos  in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uopt) ->
        let uu____29063 =
          let uu____29064 =
            let uu____29073 = elim_delayed_subst_term t  in
            (uu____29073, uopt)  in
          FStar_Syntax_Syntax.Total uu____29064  in
        mk uu____29063
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29090 =
          let uu____29091 =
            let uu____29100 = elim_delayed_subst_term t  in
            (uu____29100, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29091  in
        mk uu____29090
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3509_29109 = ct  in
          let uu____29110 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29113 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29124 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3509_29109.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3509_29109.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29110;
            FStar_Syntax_Syntax.effect_args = uu____29113;
            FStar_Syntax_Syntax.flags = uu____29124
          }  in
        mk (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29127  ->
    match uu___18_29127 with
    | FStar_Syntax_Syntax.Meta_pattern (names,args) ->
        let uu____29162 =
          let uu____29183 = FStar_List.map elim_delayed_subst_term names  in
          let uu____29192 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29183, uu____29192)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29162
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____29247 =
          let uu____29254 = elim_delayed_subst_term t  in (m, uu____29254)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____29247
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____29266 =
          let uu____29275 = elim_delayed_subst_term t  in
          (m1, m2, uu____29275)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29266
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
      (fun uu____29308  ->
         match uu____29308 with
         | (t,q) ->
             let uu____29327 = elim_delayed_subst_term t  in (uu____29327, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29355  ->
         match uu____29355 with
         | (x,q) ->
             let uu____29374 =
               let uu___3535_29375 = x  in
               let uu____29376 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3535_29375.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3535_29375.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29376
               }  in
             (uu____29374, q)) bs

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
            | (uu____29484,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  c.FStar_Syntax_Syntax.pos
            | (uu____29516,FStar_Util.Inl t) ->
                let uu____29538 =
                  let uu____29539 =
                    let uu____29554 = FStar_Syntax_Syntax.mk_Total t  in
                    (binders, uu____29554)  in
                  FStar_Syntax_Syntax.Tm_arrow uu____29539  in
                FStar_Syntax_Syntax.mk uu____29538 t.FStar_Syntax_Syntax.pos
             in
          let uu____29567 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29567 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env1 t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29599 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29672 ->
                    let uu____29673 =
                      let uu____29682 =
                        let uu____29683 = FStar_Syntax_Subst.compress t4  in
                        uu____29683.FStar_Syntax_Syntax.n  in
                      (uu____29682, tc)  in
                    (match uu____29673 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29712) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29759) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29804,FStar_Util.Inl uu____29805) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29836 -> failwith "Impossible")
                 in
              (match uu____29599 with
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
          let uu____29975 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inl t)  in
          match uu____29975 with
          | (univ_names1,binders1,tc) ->
              let uu____30049 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30049)
  
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
          let uu____30103 =
            elim_uvars_aux_tc env1 univ_names binders (FStar_Util.Inr c)  in
          match uu____30103 with
          | (univ_names1,binders1,tc) ->
              let uu____30177 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30177)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env1  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____30219 = elim_uvars_aux_t env1 univ_names binders typ  in
          (match uu____30219 with
           | (univ_names1,binders1,typ1) ->
               let uu___3618_30259 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3618_30259.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3618_30259.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3618_30259.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3618_30259.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3618_30259.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3624_30274 = s  in
          let uu____30275 =
            let uu____30276 =
              let uu____30285 = FStar_List.map (elim_uvars env1) sigs  in
              (uu____30285, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____30276  in
          {
            FStar_Syntax_Syntax.sigel = uu____30275;
            FStar_Syntax_Syntax.sigrng =
              (uu___3624_30274.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3624_30274.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3624_30274.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3624_30274.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3624_30274.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____30304 = elim_uvars_aux_t env1 univ_names [] typ  in
          (match uu____30304 with
           | (univ_names1,uu____30328,typ1) ->
               let uu___3638_30350 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3638_30350.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3638_30350.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3638_30350.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3638_30350.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3638_30350.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____30357 = elim_uvars_aux_t env1 univ_names [] typ  in
          (match uu____30357 with
           | (univ_names1,uu____30381,typ1) ->
               let uu___3649_30403 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3649_30403.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3649_30403.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3649_30403.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3649_30403.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3649_30403.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30433 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30433 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____30458 =
                            let uu____30459 =
                              let uu____30460 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env1 uu____30460  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30459
                             in
                          elim_delayed_subst_term uu____30458  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3665_30463 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3665_30463.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3665_30463.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3665_30463.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3665_30463.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3668_30464 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3668_30464.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3668_30464.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3668_30464.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3668_30464.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3668_30464.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____30473 = elim_uvars_aux_t env1 us [] t  in
          (match uu____30473 with
           | (us1,uu____30497,t1) ->
               let uu___3679_30519 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3679_30519.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3679_30519.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3679_30519.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3679_30519.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3679_30519.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30521 =
            elim_uvars_aux_t env1 ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____30521 with
           | (univs,binders,uu____30540) ->
               let uu____30561 =
                 let uu____30566 = FStar_Syntax_Subst.univ_var_opening univs
                    in
                 match uu____30566 with
                 | (univs_opening,univs1) ->
                     let uu____30589 =
                       FStar_Syntax_Subst.univ_var_closing univs1  in
                     (univs_opening, uu____30589)
                  in
               (match uu____30561 with
                | (univs_opening,univs_closing) ->
                    let uu____30592 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30598 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30599 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30598, uu____30599)  in
                    (match uu____30592 with
                     | (b_opening,b_closing) ->
                         let n = FStar_List.length univs  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30625 =
                           match uu____30625 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30643 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30643 with
                                | (us1,t1) ->
                                    let uu____30654 =
                                      let uu____30663 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30668 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30663, uu____30668)  in
                                    (match uu____30654 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30691 =
                                           let uu____30700 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____30705 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____30700, uu____30705)  in
                                         (match uu____30691 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30729 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30729
                                                 in
                                              let uu____30730 =
                                                elim_uvars_aux_t env1 [] []
                                                  t2
                                                 in
                                              (match uu____30730 with
                                               | (uu____30757,uu____30758,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30781 =
                                                       let uu____30782 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30782
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30781
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30791 =
                             elim_uvars_aux_t env1 univs binders t  in
                           match uu____30791 with
                           | (uu____30810,uu____30811,t1) -> t1  in
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
                             | uu____30887 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____30914 =
                               let uu____30915 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____30915.FStar_Syntax_Syntax.n  in
                             match uu____30914 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____30974 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31008 =
                               let uu____31009 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31009.FStar_Syntax_Syntax.n  in
                             match uu____31008 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31032) ->
                                 let uu____31057 = destruct_action_body body
                                    in
                                 (match uu____31057 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31106 ->
                                 let uu____31107 = destruct_action_body t  in
                                 (match uu____31107 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31162 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31162 with
                           | (action_univs,t) ->
                               let uu____31171 = destruct_action_typ_templ t
                                  in
                               (match uu____31171 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3763_31218 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3763_31218.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3763_31218.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3766_31220 = ed  in
                           let uu____31221 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____31222 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____31223 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3766_31220.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3766_31220.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31221;
                             FStar_Syntax_Syntax.combinators = uu____31222;
                             FStar_Syntax_Syntax.actions = uu____31223;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3766_31220.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3769_31226 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3769_31226.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3769_31226.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3769_31226.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3769_31226.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3769_31226.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31247 =
            match uu___19_31247 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____31278 = elim_uvars_aux_t env1 us [] t  in
                (match uu____31278 with
                 | (us1,uu____31310,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3784_31341 = sub_eff  in
            let uu____31342 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____31345 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3784_31341.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3784_31341.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31342;
              FStar_Syntax_Syntax.lift = uu____31345
            }  in
          let uu___3787_31348 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3787_31348.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3787_31348.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3787_31348.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3787_31348.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3787_31348.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____31358 = elim_uvars_aux_c env1 univ_names binders comp  in
          (match uu____31358 with
           | (univ_names1,binders1,comp1) ->
               let uu___3800_31398 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3800_31398.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3800_31398.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3800_31398.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3800_31398.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3800_31398.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31401 -> s
      | FStar_Syntax_Syntax.Sig_fail uu____31402 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31415 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n,p,(us_t,t),(us_ty,ty))
          ->
          let uu____31445 = elim_uvars_aux_t env1 us_t [] t  in
          (match uu____31445 with
           | (us_t1,uu____31469,t1) ->
               let uu____31491 = elim_uvars_aux_t env1 us_ty [] ty  in
               (match uu____31491 with
                | (us_ty1,uu____31515,ty1) ->
                    let uu___3827_31537 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3827_31537.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3827_31537.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3827_31537.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3827_31537.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3827_31537.FStar_Syntax_Syntax.sigopts)
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
        let uu____31588 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env1 (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____31588 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____31610 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____31610 with
             | (uu____31617,head_def) ->
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
      let uu____31621 = FStar_Syntax_Util.head_and_args t  in
      match uu____31621 with
      | (head,args) ->
          let uu____31666 =
            let uu____31667 = FStar_Syntax_Subst.compress head  in
            uu____31667.FStar_Syntax_Syntax.n  in
          (match uu____31666 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31674;
                  FStar_Syntax_Syntax.vars = uu____31675;_},us)
               -> aux fv us args
           | uu____31681 -> FStar_Pervasives_Native.None)
  