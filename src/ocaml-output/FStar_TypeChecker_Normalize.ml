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
    match projectee with | Clos _0 -> true | uu____129 -> false
  
let (__proj__Clos__item___0 :
  closure ->
    ((FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
      Prims.list * FStar_Syntax_Syntax.term * ((FStar_Syntax_Syntax.binder
      FStar_Pervasives_Native.option * closure) Prims.list *
      FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo * Prims.bool))
  = fun projectee  -> match projectee with | Clos _0 -> _0 
let (uu___is_Univ : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____241 -> false
  
let (__proj__Univ__item___0 : closure -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Dummy : closure -> Prims.bool) =
  fun projectee  ->
    match projectee with | Dummy  -> true | uu____259 -> false
  
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
  | Meta of (env * FStar_Syntax_Syntax.metadata * FStar_Range.range) 
  | Let of (env * FStar_Syntax_Syntax.binders *
  FStar_Syntax_Syntax.letbinding * FStar_Range.range) 
  | Cfg of FStar_TypeChecker_Cfg.cfg 
  | Debug of (FStar_Syntax_Syntax.term * FStar_Util.time) 
let (uu___is_Arg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arg _0 -> true | uu____428 -> false
  
let (__proj__Arg__item___0 :
  stack_elt -> (closure * FStar_Syntax_Syntax.aqual * FStar_Range.range)) =
  fun projectee  -> match projectee with | Arg _0 -> _0 
let (uu___is_UnivArgs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnivArgs _0 -> true | uu____471 -> false
  
let (__proj__UnivArgs__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.universe Prims.list * FStar_Range.range))
  = fun projectee  -> match projectee with | UnivArgs _0 -> _0 
let (uu___is_MemoLazy : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | MemoLazy _0 -> true | uu____514 -> false
  
let (__proj__MemoLazy__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.term) FStar_Syntax_Syntax.memo) =
  fun projectee  -> match projectee with | MemoLazy _0 -> _0 
let (uu___is_Match : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____559 -> false
  
let (__proj__Match__item___0 :
  stack_elt ->
    (env * branches * FStar_TypeChecker_Cfg.cfg * FStar_Range.range))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Abs : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Abs _0 -> true | uu____614 -> false
  
let (__proj__Abs__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * env *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Abs _0 -> _0 
let (uu___is_App : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | App _0 -> true | uu____677 -> false
  
let (__proj__App__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
      FStar_Range.range))
  = fun projectee  -> match projectee with | App _0 -> _0 
let (uu___is_Meta : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____726 -> false
  
let (__proj__Meta__item___0 :
  stack_elt -> (env * FStar_Syntax_Syntax.metadata * FStar_Range.range)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_Let : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Let _0 -> true | uu____771 -> false
  
let (__proj__Let__item___0 :
  stack_elt ->
    (env * FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.letbinding *
      FStar_Range.range))
  = fun projectee  -> match projectee with | Let _0 -> _0 
let (uu___is_Cfg : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cfg _0 -> true | uu____814 -> false
  
let (__proj__Cfg__item___0 : stack_elt -> FStar_TypeChecker_Cfg.cfg) =
  fun projectee  -> match projectee with | Cfg _0 -> _0 
let (uu___is_Debug : stack_elt -> Prims.bool) =
  fun projectee  ->
    match projectee with | Debug _0 -> true | uu____837 -> false
  
let (__proj__Debug__item___0 :
  stack_elt -> (FStar_Syntax_Syntax.term * FStar_Util.time)) =
  fun projectee  -> match projectee with | Debug _0 -> _0 
type stack = stack_elt Prims.list
let (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____866 = FStar_Syntax_Util.head_and_args' t  in
    match uu____866 with | (hd1,uu____882) -> hd1
  
let mk :
  'Auu____910 .
    'Auu____910 ->
      FStar_Range.range -> 'Auu____910 FStar_Syntax_Syntax.syntax
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
          let uu____953 = FStar_ST.op_Bang r  in
          match uu____953 with
          | FStar_Pervasives_Native.Some uu____979 ->
              failwith "Unexpected set_memo: thunk already evaluated"
          | FStar_Pervasives_Native.None  ->
              FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some t)
        else ()
  
let (closure_to_string : closure -> Prims.string) =
  fun uu___1_1012  ->
    match uu___1_1012 with
    | Clos (env,t,uu____1016,uu____1017) ->
        let uu____1064 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____1074 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1064 uu____1074
    | Univ uu____1077 -> "Univ"
    | Dummy  -> "dummy"
  
let (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____1103 =
      FStar_List.map
        (fun uu____1119  ->
           match uu____1119 with
           | (bopt,c) ->
               let uu____1133 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____1138 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____1133 uu____1138) env
       in
    FStar_All.pipe_right uu____1103 (FStar_String.concat "; ")
  
let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___2_1152  ->
    match uu___2_1152 with
    | Arg (c,uu____1155,uu____1156) ->
        let uu____1157 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1157
    | MemoLazy uu____1160 -> "MemoLazy"
    | Abs (uu____1168,bs,uu____1170,uu____1171,uu____1172) ->
        let uu____1177 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1177
    | UnivArgs uu____1188 -> "UnivArgs"
    | Match uu____1196 -> "Match"
    | App (uu____1206,t,uu____1208,uu____1209) ->
        let uu____1210 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1210
    | Meta (uu____1213,m,uu____1215) -> "Meta"
    | Let uu____1217 -> "Let"
    | Cfg uu____1227 -> "Cfg"
    | Debug (t,uu____1230) ->
        let uu____1231 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1231
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1245 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1245 (FStar_String.concat "; ")
  
let is_empty : 'Auu____1260 . 'Auu____1260 Prims.list -> Prims.bool =
  fun uu___3_1268  ->
    match uu___3_1268 with | [] -> true | uu____1272 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___114_1305  ->
           match () with
           | () ->
               let uu____1306 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1306) ()
      with
      | uu___113_1323 ->
          let uu____1324 =
            let uu____1326 = FStar_Syntax_Print.db_to_string x  in
            let uu____1328 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1326
              uu____1328
             in
          failwith uu____1324
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____1339 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____1339
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1346 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____1346
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1353 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____1353
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
          let uu____1391 =
            FStar_List.fold_left
              (fun uu____1417  ->
                 fun u1  ->
                   match uu____1417 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1442 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1442 with
                        | (k_u,n1) ->
                            let uu____1460 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1460
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1391 with
          | (uu____1481,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___148_1507  ->
                    match () with
                    | () ->
                        let uu____1510 =
                          let uu____1511 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____1511  in
                        (match uu____1510 with
                         | Univ u3 ->
                             ((let uu____1530 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____1530
                               then
                                 let uu____1535 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1535
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____1540 ->
                             let uu____1541 =
                               let uu____1543 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1543
                                in
                             failwith uu____1541)) ()
               with
               | uu____1553 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1559 =
                        let uu____1561 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____1561
                         in
                      failwith uu____1559))
          | FStar_Syntax_Syntax.U_unif uu____1566 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1575 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1584 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1591 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1591 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1608 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1608 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1619 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1629 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1629 with
                                  | (uu____1636,m) -> n1 <= m))
                           in
                        if uu____1619 then rest1 else us1
                    | uu____1645 -> us1)
               | uu____1651 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1655 = aux u3  in
              FStar_List.map (fun _1658  -> FStar_Syntax_Syntax.U_succ _1658)
                uu____1655
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1662 = aux u  in
           match uu____1662 with
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
            (fun uu____1823  ->
               let uu____1824 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1826 = env_to_string env  in
               let uu____1828 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____1824 uu____1826 uu____1828);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____1841 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1844 ->
                    let uu____1867 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____1867
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____1868 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____1869 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____1870 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____1871 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1896 ->
                           let uu____1909 =
                             let uu____1911 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____1913 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____1911 uu____1913
                              in
                           failwith uu____1909
                       | uu____1918 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_1954  ->
                                         match uu___4_1954 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____1961 =
                                               let uu____1968 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____1968)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____1961
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___242_1980 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___242_1980.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___242_1980.FStar_Syntax_Syntax.sort)
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
                                              | uu____1986 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____1989 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___251_1994 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___251_1994.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___251_1994.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____2015 =
                        let uu____2016 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____2016  in
                      mk uu____2015 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____2024 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2024  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____2026 = lookup_bvar env x  in
                    (match uu____2026 with
                     | Univ uu____2029 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___267_2034 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___267_2034.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___267_2034.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____2040,uu____2041) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____2132  ->
                              fun stack1  ->
                                match uu____2132 with
                                | (a,aq) ->
                                    let uu____2144 =
                                      let uu____2145 =
                                        let uu____2152 =
                                          let uu____2153 =
                                            let uu____2185 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____2185, false)  in
                                          Clos uu____2153  in
                                        (uu____2152, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2145  in
                                    uu____2144 :: stack1) args)
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
                    let uu____2353 = close_binders cfg env bs  in
                    (match uu____2353 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____2403) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env stack
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2414 =
                      let uu____2427 =
                        let uu____2436 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2436]  in
                      close_binders cfg env uu____2427  in
                    (match uu____2414 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____2481 =
                             let uu____2482 =
                               let uu____2489 =
                                 let uu____2490 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2490
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2489, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2482  in
                           mk uu____2481 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2589 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____2589
                      | FStar_Util.Inr c ->
                          let uu____2603 = close_comp cfg env c  in
                          FStar_Util.Inr uu____2603
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____2622 =
                        let uu____2623 =
                          let uu____2650 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____2650, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2623  in
                      mk uu____2622 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2696 =
                            let uu____2697 =
                              let uu____2704 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____2704, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2697  in
                          mk uu____2696 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____2759  -> dummy :: env1) env
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
                    let uu____2780 =
                      let uu____2791 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2791
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2813 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___359_2829 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___359_2829.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___359_2829.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2813))
                       in
                    (match uu____2780 with
                     | (nm,body1) ->
                         let attrs =
                           FStar_List.map
                             (non_tail_inline_closure_env cfg env0)
                             lb.FStar_Syntax_Syntax.lbattrs
                            in
                         let lb1 =
                           let uu___365_2856 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___365_2856.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___365_2856.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs = attrs;
                             FStar_Syntax_Syntax.lbpos =
                               (uu___365_2856.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2873,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____2939  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____2956 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2956
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____2971  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____2995 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2995
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___388_3006 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___388_3006.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___388_3006.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___391_3007 = lb  in
                      let uu____3008 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___391_3007.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___391_3007.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____3008;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___391_3007.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___391_3007.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____3040  -> fun env1  -> dummy :: env1)
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
            (fun uu____3132  ->
               let uu____3133 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3135 = env_to_string env  in
               let uu____3137 = stack_to_string stack  in
               let uu____3139 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____3133 uu____3135 uu____3137 uu____3139);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3146,uu____3147),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____3228 = close_binders cfg env' bs  in
               (match uu____3228 with
                | (bs1,uu____3244) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3264 =
                      let uu___449_3267 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___449_3267.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___449_3267.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____3264)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____3323 =
                 match uu____3323 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3438 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3469 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3558  ->
                                     fun uu____3559  ->
                                       match (uu____3558, uu____3559) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____3709 = norm_pat env4 p1
                                              in
                                           (match uu____3709 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____3469 with
                            | (pats1,env4) ->
                                ((let uu___486_3879 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___486_3879.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___490_3900 = x  in
                             let uu____3901 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___490_3900.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___490_3900.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3901
                             }  in
                           ((let uu___493_3915 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___493_3915.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___497_3926 = x  in
                             let uu____3927 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___497_3926.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___497_3926.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3927
                             }  in
                           ((let uu___500_3941 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___500_3941.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___506_3957 = x  in
                             let uu____3958 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___506_3957.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___506_3957.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3958
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___510_3975 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___510_3975.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____3980 = norm_pat env2 pat  in
                     (match uu____3980 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____4049 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____4049
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____4068 =
                   let uu____4069 =
                     let uu____4092 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____4092)  in
                   FStar_Syntax_Syntax.Tm_match uu____4069  in
                 mk uu____4068 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
                     let uu____4228 =
                       let uu____4249 =
                         FStar_All.pipe_right names1
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m))
                          in
                       let uu____4266 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1  ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4375  ->
                                         match uu____4375 with
                                         | (a,q) ->
                                             let uu____4402 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a
                                                in
                                             (uu____4402, q)))))
                          in
                       (uu____4249, uu____4266)  in
                     FStar_Syntax_Syntax.Meta_pattern uu____4228
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4431 =
                       let uu____4438 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4438)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4431
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4450 =
                       let uu____4459 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4459)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4450
                 | uu____4464 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____4470 -> failwith "Impossible: unexpected stack element")

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
            let uu____4486 =
              let uu____4487 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____4487  in
            FStar_Pervasives_Native.Some uu____4486
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
        let uu____4504 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4588  ->
                  fun uu____4589  ->
                    match (uu____4588, uu____4589) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___565_4729 = b  in
                          let uu____4730 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___565_4729.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___565_4729.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4730
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____4504 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4872 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4885 = inline_closure_env cfg env [] t  in
                 let uu____4886 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4885 uu____4886
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4899 = inline_closure_env cfg env [] t  in
                 let uu____4900 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4899 uu____4900
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____4954  ->
                           match uu____4954 with
                           | (a,q) ->
                               let uu____4975 =
                                 inline_closure_env cfg env [] a  in
                               (uu____4975, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_4992  ->
                           match uu___5_4992 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4996 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____4996
                           | f -> f))
                    in
                 let uu____5000 =
                   let uu___598_5001 = c1  in
                   let uu____5002 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5002;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___598_5001.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5000)

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
                   (fun uu___6_5020  ->
                      match uu___6_5020 with
                      | FStar_Syntax_Syntax.DECREASES uu____5022 -> false
                      | uu____5026 -> true))
               in
            let rc1 =
              let uu___610_5029 = rc  in
              let uu____5030 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___610_5029.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5030;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5039 -> lopt

let (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___7_5060  ->
            match uu___7_5060 with
            | FStar_Syntax_Syntax.DECREASES uu____5062 -> false
            | uu____5066 -> true))
  
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
    let uu____5113 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____5113 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5152 = FStar_Syntax_Embeddings.unembed e t  in
        uu____5152 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____5172 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____5172) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____5234  ->
           fun subst1  ->
             match uu____5234 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____5275,uu____5276)) ->
                      let uu____5337 = b  in
                      (match uu____5337 with
                       | (bv,uu____5345) ->
                           let uu____5346 =
                             let uu____5348 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5348  in
                           if uu____5346
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____5356 = unembed_binder term1  in
                              match uu____5356 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5363 =
                                      let uu___650_5364 = bv  in
                                      let uu____5365 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___650_5364.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___650_5364.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5365
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5363
                                     in
                                  let b_for_x =
                                    let uu____5371 =
                                      let uu____5378 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5378)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5371  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___8_5394  ->
                                         match uu___8_5394 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5396,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5398;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5399;_})
                                             ->
                                             let uu____5404 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5404
                                         | uu____5406 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____5408 -> subst1)) env []
  
let reduce_primops :
  'Auu____5430 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5430)
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
            (let uu____5482 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5482 with
             | (head1,args) ->
                 let uu____5527 =
                   let uu____5528 = FStar_Syntax_Util.un_uinst head1  in
                   uu____5528.FStar_Syntax_Syntax.n  in
                 (match uu____5527 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5534 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5534 with
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
                                (fun uu____5557  ->
                                   let uu____5558 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5560 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5562 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5558 uu____5560 uu____5562);
                              tm)
                           else
                             (let uu____5567 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5567 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5653  ->
                                        let uu____5654 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5654);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5659  ->
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
                                           (fun uu____5673  ->
                                              let uu____5674 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5674);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5682  ->
                                              let uu____5683 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5685 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5683 uu____5685);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5688 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5692  ->
                                 let uu____5693 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5693);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5699  ->
                            let uu____5700 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5700);
                       (match args with
                        | (a1,uu____5706)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5731 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5745  ->
                            let uu____5746 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5746);
                       (match args with
                        | (t,uu____5752)::(r,uu____5754)::[] ->
                            let uu____5795 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5795 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5801 -> tm))
                  | uu____5812 -> tm))
  
let reduce_equality :
  'Auu____5823 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5823)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___738_5872 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___740_5875 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___740_5875.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___740_5875.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___740_5875.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___740_5875.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___740_5875.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___740_5875.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___740_5875.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___740_5875.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___740_5875.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___740_5875.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___740_5875.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___740_5875.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___740_5875.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___740_5875.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___740_5875.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___740_5875.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___740_5875.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___740_5875.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___740_5875.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___740_5875.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___740_5875.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___740_5875.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___740_5875.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___740_5875.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___740_5875.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___738_5872.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___738_5872.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___738_5872.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___738_5872.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___738_5872.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___738_5872.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___738_5872.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____5886 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____5897 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____5908 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____5929 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____5929
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____5961 =
        let uu____5962 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5962.FStar_Syntax_Syntax.n  in
      match uu____5961 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu____5971 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____5980 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____5980)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____5993 =
        let uu____5994 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5994.FStar_Syntax_Syntax.n  in
      match uu____5993 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6052 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____6052 rest
           | uu____6079 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6119 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____6119 rest
           | uu____6138 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____6212 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____6212 rest
           | uu____6247 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6249 ->
          let uu____6250 =
            let uu____6252 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6252
             in
          failwith uu____6250
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6273  ->
    match uu___9_6273 with
    | FStar_Syntax_Embeddings.Zeta  -> [FStar_TypeChecker_Env.Zeta]
    | FStar_Syntax_Embeddings.Iota  -> [FStar_TypeChecker_Env.Iota]
    | FStar_Syntax_Embeddings.Delta  ->
        [FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant]
    | FStar_Syntax_Embeddings.Simpl  -> [FStar_TypeChecker_Env.Simplify]
    | FStar_Syntax_Embeddings.Weak  -> [FStar_TypeChecker_Env.Weak]
    | FStar_Syntax_Embeddings.HNF  -> [FStar_TypeChecker_Env.HNF]
    | FStar_Syntax_Embeddings.Primops  -> [FStar_TypeChecker_Env.Primops]
    | FStar_Syntax_Embeddings.Reify  -> [FStar_TypeChecker_Env.Reify]
    | FStar_Syntax_Embeddings.UnfoldOnly names1 ->
        let uu____6280 =
          let uu____6283 =
            let uu____6284 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6284  in
          [uu____6283]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6280
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____6292 =
          let uu____6295 =
            let uu____6296 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____6296  in
          [uu____6295]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6292
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____6304 =
          let uu____6307 =
            let uu____6308 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6308  in
          [uu____6307]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6304
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  =
  fun s  ->
    let s1 = FStar_List.concatMap tr_norm_step s  in
    let add_exclude s2 z =
      let uu____6344 =
        FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s2  in
      if uu____6344 then s2 else (FStar_TypeChecker_Env.Exclude z) :: s2  in
    let s2 = FStar_TypeChecker_Env.Beta :: s1  in
    let s3 = add_exclude s2 FStar_TypeChecker_Env.Zeta  in
    let s4 = add_exclude s3 FStar_TypeChecker_Env.Iota  in s4
  
let get_norm_request :
  'Auu____6369 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____6369) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6420 =
            let uu____6425 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6425 s  in
          match uu____6420 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6441 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6441
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
        | uu____6476::(tm,uu____6478)::[] ->
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
        | (tm,uu____6507)::[] ->
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
        | (steps,uu____6528)::uu____6529::(tm,uu____6531)::[] ->
            let uu____6552 =
              let uu____6557 = full_norm steps  in parse_steps uu____6557  in
            (match uu____6552 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s), tm))
        | uu____6587 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6619 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6626  ->
                    match uu___10_6626 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6628 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6630 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6634 -> true
                    | uu____6638 -> false))
             in
          if uu____6619
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6648  ->
             let uu____6649 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6649);
        (let tm_norm =
           let uu____6653 =
             let uu____6668 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6668.FStar_TypeChecker_Env.nbe  in
           uu____6653 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6672  ->
              let uu____6673 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6673);
         tm_norm)
  
let firstn :
  'Auu____6683 .
    Prims.int ->
      'Auu____6683 Prims.list ->
        ('Auu____6683 Prims.list * 'Auu____6683 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___11_6740 =
        match uu___11_6740 with
        | (MemoLazy uu____6745)::s -> drop_irrel s
        | (UnivArgs uu____6755)::s -> drop_irrel s
        | s -> s  in
      let uu____6768 = drop_irrel stack  in
      match uu____6768 with
      | (App
          (uu____6772,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6773;
                        FStar_Syntax_Syntax.vars = uu____6774;_},uu____6775,uu____6776))::uu____6777
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6782 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6811) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6821) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6842  ->
                  match uu____6842 with
                  | (a,uu____6853) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6864 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6889 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6891 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6905 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6907 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6909 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6911 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6913 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6916 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6924 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6932 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6947 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6967 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6983 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6991 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7063  ->
                   match uu____7063 with
                   | (a,uu____7074) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7085) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____7184,args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7239  ->
                        match uu____7239 with
                        | (a,uu____7250) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7259,uu____7260,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7266,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7272 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7282 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7284 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7295 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7306 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7317 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7328 -> false
  
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
            let uu____7361 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7361 with
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
              (fun uu____7560  ->
                 fun uu____7561  ->
                   match (uu____7560, uu____7561) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7667 =
            match uu____7667 with
            | (x,y,z) ->
                let uu____7687 = FStar_Util.string_of_bool x  in
                let uu____7689 = FStar_Util.string_of_bool y  in
                let uu____7691 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7687 uu____7689
                  uu____7691
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7719  ->
                    let uu____7720 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7722 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7720 uu____7722);
               if b then reif else no)
            else
              if
                (let uu____7737 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7737)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7742  ->
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
                          ((is_rec,uu____7777),uu____7778);
                        FStar_Syntax_Syntax.sigrng = uu____7779;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7781;
                        FStar_Syntax_Syntax.sigattrs = uu____7782;
                        FStar_Syntax_Syntax.sigopts = uu____7783;_},uu____7784),uu____7785),uu____7786,uu____7787,uu____7788)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7897  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7899,uu____7900,uu____7901,uu____7902) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7969  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7972),uu____7973);
                        FStar_Syntax_Syntax.sigrng = uu____7974;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7976;
                        FStar_Syntax_Syntax.sigattrs = uu____7977;
                        FStar_Syntax_Syntax.sigopts = uu____7978;_},uu____7979),uu____7980),uu____7981,uu____7982,uu____7983)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8092  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8094,FStar_Pervasives_Native.Some
                    uu____8095,uu____8096,uu____8097) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8165  ->
                           let uu____8166 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8166);
                      (let uu____8169 =
                         let uu____8181 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8207 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8207
                            in
                         let uu____8219 =
                           let uu____8231 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8257 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8257
                              in
                           let uu____8273 =
                             let uu____8285 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8311 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8311
                                in
                             [uu____8285]  in
                           uu____8231 :: uu____8273  in
                         uu____8181 :: uu____8219  in
                       comb_or uu____8169))
                 | (uu____8359,uu____8360,FStar_Pervasives_Native.Some
                    uu____8361,uu____8362) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8430  ->
                           let uu____8431 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8431);
                      (let uu____8434 =
                         let uu____8446 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8472 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8472
                            in
                         let uu____8484 =
                           let uu____8496 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8522 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8522
                              in
                           let uu____8538 =
                             let uu____8550 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8576 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8576
                                in
                             [uu____8550]  in
                           uu____8496 :: uu____8538  in
                         uu____8446 :: uu____8484  in
                       comb_or uu____8434))
                 | (uu____8624,uu____8625,uu____8626,FStar_Pervasives_Native.Some
                    uu____8627) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8695  ->
                           let uu____8696 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8696);
                      (let uu____8699 =
                         let uu____8711 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8737 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8737
                            in
                         let uu____8749 =
                           let uu____8761 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8787 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8787
                              in
                           let uu____8803 =
                             let uu____8815 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8841 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8841
                                in
                             [uu____8815]  in
                           uu____8761 :: uu____8803  in
                         uu____8711 :: uu____8749  in
                       comb_or uu____8699))
                 | uu____8889 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8935  ->
                           let uu____8936 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____8938 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____8940 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____8936 uu____8938 uu____8940);
                      (let uu____8943 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_8949  ->
                                 match uu___12_8949 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____8955 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____8955 l))
                          in
                       FStar_All.pipe_left yesno uu____8943)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____8971  ->
               let uu____8972 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____8974 =
                 let uu____8976 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____8976  in
               let uu____8977 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____8972 uu____8974 uu____8977);
          (match res with
           | (false ,uu____8980,uu____8981) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____9006 ->
               let uu____9016 =
                 let uu____9018 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9018
                  in
               FStar_All.pipe_left failwith uu____9016)
  
let decide_unfolding :
  'Auu____9037 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____9037 ->
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
                    let uu___1148_9106 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1150_9109 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1150_9109.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1150_9109.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1148_9106.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1148_9106.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1148_9106.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1148_9106.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1148_9106.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1148_9106.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1148_9106.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1148_9106.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____9171 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____9171
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9183 =
                      let uu____9190 =
                        let uu____9191 =
                          let uu____9192 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____9192  in
                        FStar_Syntax_Syntax.Tm_constant uu____9191  in
                      FStar_Syntax_Syntax.mk uu____9190  in
                    uu____9183 FStar_Pervasives_Native.None
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
    let uu____9258 =
      let uu____9259 = FStar_Syntax_Subst.compress t  in
      uu____9259.FStar_Syntax_Syntax.n  in
    match uu____9258 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9290 =
          let uu____9291 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9291.FStar_Syntax_Syntax.n  in
        (match uu____9290 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9308 =
                 let uu____9315 =
                   let uu____9326 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9326 FStar_List.tl  in
                 FStar_All.pipe_right uu____9315 FStar_List.hd  in
               FStar_All.pipe_right uu____9308 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9425 -> FStar_Pervasives_Native.None)
    | uu____9426 -> FStar_Pervasives_Native.None
  
let is_wp_req_ens_commutation :
  'Auu____9434 .
    'Auu____9434 ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun t  ->
      let is_fv t1 lid =
        let uu____9459 =
          let uu____9460 = FStar_Syntax_Subst.compress t1  in
          uu____9460.FStar_Syntax_Syntax.n  in
        match uu____9459 with
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____9465) ->
            let uu____9470 =
              let uu____9471 = FStar_Syntax_Subst.compress t2  in
              uu____9471.FStar_Syntax_Syntax.n  in
            (match uu____9470 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv lid
             | uu____9476 -> false)
        | uu____9478 -> false  in
      let us_of t1 =
        let uu____9486 =
          let uu____9487 = FStar_Syntax_Subst.compress t1  in
          uu____9487.FStar_Syntax_Syntax.n  in
        match uu____9486 with
        | FStar_Syntax_Syntax.Tm_uinst (uu____9490,us) -> us
        | uu____9496 ->
            failwith "Impossible! us_of called with a non Tm_uinst term"
         in
      let mk_app1 lid us args r =
        let uu____9519 =
          let uu____9520 =
            let uu____9521 =
              FStar_Syntax_Syntax.lid_as_fv lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                FStar_Pervasives_Native.None
               in
            FStar_All.pipe_right uu____9521 FStar_Syntax_Syntax.fv_to_tm  in
          FStar_All.pipe_right uu____9520
            (fun t1  -> FStar_Syntax_Syntax.mk_Tm_uinst t1 us)
           in
        FStar_All.pipe_right uu____9519
          (fun f  ->
             FStar_Syntax_Syntax.mk_Tm_app f args
               FStar_Pervasives_Native.None r)
         in
      let reduce_as_requires args r =
        if (FStar_List.length args) <> (Prims.of_int (2))
        then FStar_Pervasives_Native.None
        else
          (let uu____9557 = args  in
           match uu____9557 with
           | uu____9560::(wp,uu____9562)::[] ->
               let uu____9603 =
                 let uu____9604 = FStar_Syntax_Subst.compress wp  in
                 uu____9604.FStar_Syntax_Syntax.n  in
               (match uu____9603 with
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.as_wp ->
                    let uu____9635 = args1  in
                    (match uu____9635 with
                     | uu____9648::(req,uu____9650)::uu____9651::[] ->
                         FStar_Pervasives_Native.Some req)
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_return_lid ->
                    let uu____9734 =
                      let uu____9735 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_return uu____9735
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9738  -> FStar_Pervasives_Native.Some _9738)
                      uu____9734
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_bind_lid ->
                    let uu____9765 =
                      let uu____9766 = us_of head1  in
                      let uu____9767 =
                        FStar_All.pipe_right args1 FStar_List.tl  in
                      mk_app1 FStar_Parser_Const.as_req_bind uu____9766
                        uu____9767 r
                       in
                    FStar_All.pipe_left
                      (fun _9788  -> FStar_Pervasives_Native.Some _9788)
                      uu____9765
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_weaken_wp_lid ->
                    let uu____9815 =
                      let uu____9816 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_weaken uu____9816
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9819  -> FStar_Pervasives_Native.Some _9819)
                      uu____9815
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_strengthen_wp_lid ->
                    let uu____9846 =
                      let uu____9847 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_strengthen uu____9847
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9850  -> FStar_Pervasives_Native.Some _9850)
                      uu____9846
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_if_then_else_lid ->
                    let uu____9877 =
                      let uu____9878 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_if_then_else
                        uu____9878 args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9881  -> FStar_Pervasives_Native.Some _9881)
                      uu____9877
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_ite_lid ->
                    let uu____9908 =
                      let uu____9909 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_ite uu____9909 args1
                        r
                       in
                    FStar_All.pipe_left
                      (fun _9912  -> FStar_Pervasives_Native.Some _9912)
                      uu____9908
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_close_lid ->
                    let uu____9939 =
                      let uu____9940 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_close uu____9940
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9943  -> FStar_Pervasives_Native.Some _9943)
                      uu____9939
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_null_lid ->
                    let uu____9970 =
                      let uu____9971 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_null uu____9971 args1
                        r
                       in
                    FStar_All.pipe_left
                      (fun _9974  -> FStar_Pervasives_Native.Some _9974)
                      uu____9970
                | uu____9975 -> FStar_Pervasives_Native.None))
         in
      let reduce_as_ensures args r =
        if
          ((FStar_List.length args) <> (Prims.of_int (2))) &&
            ((FStar_List.length args) <> (Prims.of_int (3)))
        then FStar_Pervasives_Native.None
        else
          (let wp =
             if (FStar_List.length args) = (Prims.of_int (2))
             then
               let uu____10026 = args  in
               match uu____10026 with
               | uu____10027::(wp,uu____10029)::[] -> wp
             else
               (let uu____10072 = args  in
                match uu____10072 with
                | uu____10073::(wp,uu____10075)::uu____10076::[] -> wp)
              in
           let uu____10133 =
             let uu____10134 = FStar_Syntax_Subst.compress wp  in
             uu____10134.FStar_Syntax_Syntax.n  in
           match uu____10133 with
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.as_wp ->
               let uu____10165 = args1  in
               (match uu____10165 with
                | uu____10178::uu____10179::(ens,uu____10181)::[] ->
                    FStar_Pervasives_Native.Some ens)
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_return_lid ->
               let uu____10264 =
                 let uu____10265 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_return uu____10265 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10268  -> FStar_Pervasives_Native.Some _10268)
                 uu____10264
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_bind_lid ->
               let uu____10295 =
                 let uu____10296 = us_of head1  in
                 let uu____10297 = FStar_All.pipe_right args1 FStar_List.tl
                    in
                 mk_app1 FStar_Parser_Const.as_ens_bind uu____10296
                   uu____10297 r
                  in
               FStar_All.pipe_left
                 (fun _10318  -> FStar_Pervasives_Native.Some _10318)
                 uu____10295
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_weaken_wp_lid ->
               let uu____10345 =
                 let uu____10346 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_weaken uu____10346 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10349  -> FStar_Pervasives_Native.Some _10349)
                 uu____10345
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_strengthen_wp_lid ->
               let uu____10376 =
                 let uu____10377 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_strengthen uu____10377
                   args1 r
                  in
               FStar_All.pipe_left
                 (fun _10380  -> FStar_Pervasives_Native.Some _10380)
                 uu____10376
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_if_then_else_lid ->
               let uu____10407 =
                 let uu____10408 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_if_then_else uu____10408
                   args1 r
                  in
               FStar_All.pipe_left
                 (fun _10411  -> FStar_Pervasives_Native.Some _10411)
                 uu____10407
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_ite_lid ->
               let uu____10438 =
                 let uu____10439 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_ite uu____10439 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10442  -> FStar_Pervasives_Native.Some _10442)
                 uu____10438
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_close_lid ->
               let uu____10469 =
                 let uu____10470 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_close uu____10470 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10473  -> FStar_Pervasives_Native.Some _10473)
                 uu____10469
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_null_lid ->
               let uu____10500 =
                 let uu____10501 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_null uu____10501 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10504  -> FStar_Pervasives_Native.Some _10504)
                 uu____10500
           | uu____10505 -> FStar_Pervasives_Native.None)
         in
      let uu____10506 =
        let uu____10507 = FStar_Syntax_Subst.compress t  in
        uu____10507.FStar_Syntax_Syntax.n  in
      match uu____10506 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) when
          is_fv head1 FStar_Parser_Const.as_requires_opaque ->
          reduce_as_requires args t.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) when
          is_fv head1 FStar_Parser_Const.as_ensures_opaque ->
          reduce_as_ensures args t.FStar_Syntax_Syntax.pos
      | uu____10564 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____10843 ->
                   let uu____10866 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____10866
               | uu____10869 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____10879  ->
               let uu____10880 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____10882 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____10884 = FStar_Syntax_Print.term_to_string t1  in
               let uu____10886 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____10894 =
                 let uu____10896 =
                   let uu____10899 = firstn (Prims.of_int (4)) stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10899
                    in
                 stack_to_string uu____10896  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____10880 uu____10882 uu____10884 uu____10886 uu____10894);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____10927  ->
               let uu____10928 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____10928);
          (let t_opt = is_wp_req_ens_commutation cfg t1  in
           let uu____10934 = FStar_All.pipe_right t_opt FStar_Util.is_some
              in
           if uu____10934
           then
             ((let uu____10941 =
                 FStar_All.pipe_left
                   (FStar_TypeChecker_Env.debug
                      cfg.FStar_TypeChecker_Cfg.tcenv)
                   (FStar_Options.Other "WPReqEns")
                  in
               if uu____10941
               then
                 let uu____10946 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10948 =
                   let uu____10950 =
                     FStar_All.pipe_right t_opt FStar_Util.must  in
                   FStar_All.pipe_right uu____10950
                     FStar_Syntax_Print.term_to_string
                    in
                 FStar_Util.print2
                   "Norm request identified as wp_req_ens commutation{, \n\nreduced %s \n\nto\n\n %s\n"
                   uu____10946 uu____10948
               else ());
              (let t2 = FStar_All.pipe_right t_opt FStar_Util.must  in
               let cfg_restricted =
                 FStar_TypeChecker_Cfg.config' []
                   [FStar_TypeChecker_Env.UnfoldAttr
                      [FStar_Parser_Const.wp_req_ens_attr]]
                   cfg.FStar_TypeChecker_Cfg.tcenv
                  in
               let t3 = norm cfg_restricted env [] t2  in
               (let uu____10963 =
                  FStar_All.pipe_left
                    (FStar_TypeChecker_Env.debug
                       cfg.FStar_TypeChecker_Cfg.tcenv)
                    (FStar_Options.Other "WPReqEns")
                   in
                if uu____10963
                then
                  let uu____10968 = FStar_Syntax_Print.term_to_string t3  in
                  FStar_Util.print1
                    "After norm in a restricted environment, t : %s\n}"
                    uu____10968
                else ());
               norm cfg env stack t3))
           else
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10978  ->
                        let uu____10979 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10979);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_constant uu____10982 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10986  ->
                        let uu____10987 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10987);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_name uu____10990 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10994  ->
                        let uu____10995 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10995);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_lazy uu____10998 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11002  ->
                        let uu____11003 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11003);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = uu____11006;
                    FStar_Syntax_Syntax.fv_delta = uu____11007;
                    FStar_Syntax_Syntax.fv_qual =
                      FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Data_ctor );_}
                  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11011  ->
                        let uu____11012 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11012);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = uu____11015;
                    FStar_Syntax_Syntax.fv_delta = uu____11016;
                    FStar_Syntax_Syntax.fv_qual =
                      FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor uu____11017);_}
                  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11027  ->
                        let uu____11028 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11028);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                  let qninfo =
                    FStar_TypeChecker_Env.lookup_qname
                      cfg.FStar_TypeChecker_Cfg.tcenv lid
                     in
                  let uu____11034 =
                    FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
                  (match uu____11034 with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Delta_constant_at_level _11037)
                       when _11037 = Prims.int_zero ->
                       (FStar_TypeChecker_Cfg.log_unfolding cfg
                          (fun uu____11041  ->
                             let uu____11042 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                               uu____11042);
                        rebuild cfg env stack t1)
                   | uu____11045 ->
                       let uu____11048 =
                         decide_unfolding cfg env stack
                           t1.FStar_Syntax_Syntax.pos fv qninfo
                          in
                       (match uu____11048 with
                        | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                            do_unfold_fv cfg1 env stack1 t1 qninfo fv
                        | FStar_Pervasives_Native.None  ->
                            rebuild cfg env stack t1))
              | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
                  let qi1 =
                    FStar_Syntax_Syntax.on_antiquoted (norm cfg env []) qi
                     in
                  let t2 =
                    mk (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                      t1.FStar_Syntax_Syntax.pos
                     in
                  let uu____11087 = closure_as_term cfg env t2  in
                  rebuild cfg env stack uu____11087
              | FStar_Syntax_Syntax.Tm_app (hd1,args) when
                  (should_consider_norm_requests cfg) &&
                    (let uu____11115 = is_norm_request hd1 args  in
                     uu____11115 = Norm_request_requires_rejig)
                  ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     FStar_Util.print_string "Rejigging norm request ... \n"
                   else ();
                   (let uu____11121 = rejig_norm_request hd1 args  in
                    norm cfg env stack uu____11121))
              | FStar_Syntax_Syntax.Tm_app (hd1,args) when
                  (should_consider_norm_requests cfg) &&
                    (let uu____11149 = is_norm_request hd1 args  in
                     uu____11149 = Norm_request_ready)
                  ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     FStar_Util.print_string "Potential norm request ... \n"
                   else ();
                   (let cfg' =
                      let uu___1418_11156 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (let uu___1420_11159 =
                             cfg.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               false;
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1420_11159.FStar_TypeChecker_Cfg.for_extraction)
                           });
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1418_11156.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1418_11156.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          [FStar_TypeChecker_Env.Unfold
                             FStar_Syntax_Syntax.delta_constant];
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1418_11156.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1418_11156.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1418_11156.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___1418_11156.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let uu____11166 =
                      get_norm_request cfg (norm cfg' env []) args  in
                    match uu____11166 with
                    | FStar_Pervasives_Native.None  ->
                        (if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           FStar_Util.print_string "Norm request None ... \n"
                         else ();
                         (let stack1 =
                            FStar_All.pipe_right stack
                              (FStar_List.fold_right
                                 (fun uu____11202  ->
                                    fun stack1  ->
                                      match uu____11202 with
                                      | (a,aq) ->
                                          let uu____11214 =
                                            let uu____11215 =
                                              let uu____11222 =
                                                let uu____11223 =
                                                  let uu____11255 =
                                                    FStar_Util.mk_ref
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  (env, a, uu____11255,
                                                    false)
                                                   in
                                                Clos uu____11223  in
                                              (uu____11222, aq,
                                                (t1.FStar_Syntax_Syntax.pos))
                                               in
                                            Arg uu____11215  in
                                          uu____11214 :: stack1) args)
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____11323  ->
                               let uu____11324 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length args)
                                  in
                               FStar_Util.print1 "\tPushed %s arguments\n"
                                 uu____11324);
                          norm cfg env stack1 hd1))
                    | FStar_Pervasives_Native.Some (s,tm) when
                        is_nbe_request s ->
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
                            let uu____11356 =
                              let uu____11358 =
                                let uu____11360 =
                                  FStar_Util.time_diff start fin  in
                                FStar_Pervasives_Native.snd uu____11360  in
                              FStar_Util.string_of_int uu____11358  in
                            let uu____11367 =
                              FStar_Syntax_Print.term_to_string tm'  in
                            let uu____11369 =
                              FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                            let uu____11371 =
                              FStar_Syntax_Print.term_to_string tm_norm  in
                            FStar_Util.print4
                              "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                              uu____11356 uu____11367 uu____11369 uu____11371)
                         else ();
                         rebuild cfg env stack tm_norm)
                    | FStar_Pervasives_Native.Some (s,tm) ->
                        let delta_level =
                          let uu____11391 =
                            FStar_All.pipe_right s
                              (FStar_Util.for_some
                                 (fun uu___13_11398  ->
                                    match uu___13_11398 with
                                    | FStar_TypeChecker_Env.UnfoldUntil
                                        uu____11400 -> true
                                    | FStar_TypeChecker_Env.UnfoldOnly
                                        uu____11402 -> true
                                    | FStar_TypeChecker_Env.UnfoldFully
                                        uu____11406 -> true
                                    | uu____11410 -> false))
                             in
                          if uu____11391
                          then
                            [FStar_TypeChecker_Env.Unfold
                               FStar_Syntax_Syntax.delta_constant]
                          else [FStar_TypeChecker_Env.NoDelta]  in
                        let cfg'1 =
                          let uu___1458_11418 = cfg  in
                          let uu____11419 =
                            let uu___1460_11420 =
                              FStar_TypeChecker_Cfg.to_fsteps s  in
                            {
                              FStar_TypeChecker_Cfg.beta =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.beta);
                              FStar_TypeChecker_Cfg.iota =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.iota);
                              FStar_TypeChecker_Cfg.zeta =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.zeta);
                              FStar_TypeChecker_Cfg.weak =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.weak);
                              FStar_TypeChecker_Cfg.hnf =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.hnf);
                              FStar_TypeChecker_Cfg.primops =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.primops);
                              FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                              FStar_TypeChecker_Cfg.unfold_until =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.unfold_until);
                              FStar_TypeChecker_Cfg.unfold_only =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.unfold_only);
                              FStar_TypeChecker_Cfg.unfold_fully =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.unfold_fully);
                              FStar_TypeChecker_Cfg.unfold_attr =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.unfold_attr);
                              FStar_TypeChecker_Cfg.unfold_tac =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.unfold_tac);
                              FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                              FStar_TypeChecker_Cfg.simplify =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.simplify);
                              FStar_TypeChecker_Cfg.erase_universes =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.erase_universes);
                              FStar_TypeChecker_Cfg.allow_unbound_universes =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.allow_unbound_universes);
                              FStar_TypeChecker_Cfg.reify_ =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.reify_);
                              FStar_TypeChecker_Cfg.compress_uvars =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.compress_uvars);
                              FStar_TypeChecker_Cfg.no_full_norm =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.no_full_norm);
                              FStar_TypeChecker_Cfg.check_no_uvars =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.check_no_uvars);
                              FStar_TypeChecker_Cfg.unmeta =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.unmeta);
                              FStar_TypeChecker_Cfg.unascribe =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.unascribe);
                              FStar_TypeChecker_Cfg.in_full_norm_request =
                                true;
                              FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                              FStar_TypeChecker_Cfg.nbe_step =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.nbe_step);
                              FStar_TypeChecker_Cfg.for_extraction =
                                (uu___1460_11420.FStar_TypeChecker_Cfg.for_extraction)
                            }  in
                          {
                            FStar_TypeChecker_Cfg.steps = uu____11419;
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___1458_11418.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___1458_11418.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level = delta_level;
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___1458_11418.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___1458_11418.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___1458_11418.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                            FStar_TypeChecker_Cfg.reifying =
                              (uu___1458_11418.FStar_TypeChecker_Cfg.reifying)
                          }  in
                        let stack' =
                          let tail1 = (Cfg cfg) :: stack  in
                          if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                          then
                            let uu____11428 =
                              let uu____11429 =
                                let uu____11434 = FStar_Util.now ()  in
                                (tm, uu____11434)  in
                              Debug uu____11429  in
                            uu____11428 :: tail1
                          else tail1  in
                        norm cfg'1 env stack' tm))
              | FStar_Syntax_Syntax.Tm_type u ->
                  let u1 = norm_universe cfg env u  in
                  let uu____11439 =
                    mk (FStar_Syntax_Syntax.Tm_type u1)
                      t1.FStar_Syntax_Syntax.pos
                     in
                  rebuild cfg env stack uu____11439
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                  then norm cfg env stack t'
                  else
                    (let us1 =
                       let uu____11450 =
                         let uu____11457 =
                           FStar_List.map (norm_universe cfg env) us  in
                         (uu____11457, (t1.FStar_Syntax_Syntax.pos))  in
                       UnivArgs uu____11450  in
                     let stack1 = us1 :: stack  in norm cfg env stack1 t')
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____11466 = lookup_bvar env x  in
                  (match uu____11466 with
                   | Univ uu____11467 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> failwith "Term variable not found"
                   | Clos (env1,t0,r,fix) ->
                       if
                         (Prims.op_Negation fix) ||
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                       then
                         let uu____11521 = FStar_ST.op_Bang r  in
                         (match uu____11521 with
                          | FStar_Pervasives_Native.Some (env2,t') ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11617  ->
                                    let uu____11618 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____11620 =
                                      FStar_Syntax_Print.term_to_string t'
                                       in
                                    FStar_Util.print2
                                      "Lazy hit: %s cached to %s\n"
                                      uu____11618 uu____11620);
                               (let uu____11623 = maybe_weakly_reduced t'  in
                                if uu____11623
                                then
                                  match stack with
                                  | [] when
                                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                        ||
                                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                      -> rebuild cfg env2 stack t'
                                  | uu____11626 -> norm cfg env2 stack t'
                                else rebuild cfg env2 stack t'))
                          | FStar_Pervasives_Native.None  ->
                              norm cfg env1 ((MemoLazy r) :: stack) t0)
                       else norm cfg env1 stack t0)
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  (match stack with
                   | (UnivArgs uu____11670)::uu____11671 ->
                       failwith
                         "Ill-typed term: universes cannot be applied to term abstraction"
                   | (Arg (c,uu____11682,uu____11683))::stack_rest ->
                       (match c with
                        | Univ uu____11687 ->
                            norm cfg ((FStar_Pervasives_Native.None, c) ::
                              env) stack_rest t1
                        | uu____11696 ->
                            (match bs with
                             | [] -> failwith "Impossible"
                             | b::[] ->
                                 (FStar_TypeChecker_Cfg.log cfg
                                    (fun uu____11726  ->
                                       let uu____11727 = closure_to_string c
                                          in
                                       FStar_Util.print1 "\tShifted %s\n"
                                         uu____11727);
                                  norm cfg
                                    (((FStar_Pervasives_Native.Some b), c) ::
                                    env) stack_rest body)
                             | b::tl1 ->
                                 (FStar_TypeChecker_Cfg.log cfg
                                    (fun uu____11763  ->
                                       let uu____11764 = closure_to_string c
                                          in
                                       FStar_Util.print1 "\tShifted %s\n"
                                         uu____11764);
                                  (let body1 =
                                     mk
                                       (FStar_Syntax_Syntax.Tm_abs
                                          (tl1, body, lopt))
                                       t1.FStar_Syntax_Syntax.pos
                                      in
                                   norm cfg
                                     (((FStar_Pervasives_Native.Some b), c)
                                     :: env) stack_rest body1))))
                   | (Cfg cfg1)::stack1 -> norm cfg1 env stack1 t1
                   | (MemoLazy r)::stack1 ->
                       (set_memo cfg r (env, t1);
                        FStar_TypeChecker_Cfg.log cfg
                          (fun uu____11812  ->
                             let uu____11813 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.print1 "\tSet memo %s\n" uu____11813);
                        norm cfg env stack1 t1)
                   | (Match uu____11816)::uu____11817 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____11832 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____11832 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____11868  -> dummy :: env1)
                                     env)
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
                                             let uu____11912 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____11912)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1578_11920 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1578_11920.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1578_11920.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____11921 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11927  ->
                                    let uu____11928 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____11928);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1585_11943 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1585_11943.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1585_11943.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1585_11943.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1585_11943.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1585_11943.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1585_11943.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1585_11943.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1585_11943.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Debug uu____11947)::uu____11948 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____11959 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____11959 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____11995  -> dummy :: env1)
                                     env)
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
                                             let uu____12039 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12039)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1578_12047 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1578_12047.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1578_12047.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12048 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12054  ->
                                    let uu____12055 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12055);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1585_12070 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1585_12070.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1585_12070.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1585_12070.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1585_12070.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1585_12070.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1585_12070.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1585_12070.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1585_12070.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Meta uu____12074)::uu____12075 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12088 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12088 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12124  -> dummy :: env1)
                                     env)
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
                                             let uu____12168 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12168)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1578_12176 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1578_12176.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1578_12176.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12177 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12183  ->
                                    let uu____12184 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12184);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1585_12199 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1585_12199.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1585_12199.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1585_12199.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1585_12199.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1585_12199.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1585_12199.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1585_12199.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1585_12199.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Let uu____12203)::uu____12204 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12219 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12219 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12255  -> dummy :: env1)
                                     env)
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
                                             let uu____12299 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12299)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1578_12307 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1578_12307.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1578_12307.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12308 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12314  ->
                                    let uu____12315 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12315);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1585_12330 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1585_12330.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1585_12330.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1585_12330.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1585_12330.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1585_12330.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1585_12330.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1585_12330.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1585_12330.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (App uu____12334)::uu____12335 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12350 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12350 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12386  -> dummy :: env1)
                                     env)
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
                                             let uu____12430 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12430)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1578_12438 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1578_12438.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1578_12438.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12439 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12445  ->
                                    let uu____12446 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12446);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1585_12461 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1585_12461.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1585_12461.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1585_12461.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1585_12461.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1585_12461.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1585_12461.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1585_12461.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1585_12461.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Abs uu____12465)::uu____12466 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12485 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12485 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12521  -> dummy :: env1)
                                     env)
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
                                             let uu____12565 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12565)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1578_12573 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1578_12573.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1578_12573.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12574 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12580  ->
                                    let uu____12581 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12581);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1585_12596 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1585_12596.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1585_12596.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1585_12596.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1585_12596.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1585_12596.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1585_12596.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1585_12596.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1585_12596.FStar_TypeChecker_Cfg.reifying)
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
                         (let uu____12604 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12604 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12640  -> dummy :: env1)
                                     env)
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
                                             let uu____12684 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12684)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1578_12692 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1578_12692.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1578_12692.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12693 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12699  ->
                                    let uu____12700 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12700);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1585_12715 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1585_12715.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1585_12715.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1585_12715.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1585_12715.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1585_12715.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1585_12715.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1585_12715.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1585_12715.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1))))
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let strict_args =
                    let uu____12751 =
                      let uu____12752 = FStar_Syntax_Util.un_uinst head1  in
                      uu____12752.FStar_Syntax_Syntax.n  in
                    match uu____12751 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_TypeChecker_Env.fv_has_strict_args
                          cfg.FStar_TypeChecker_Cfg.tcenv fv
                    | uu____12761 -> FStar_Pervasives_Native.None  in
                  (match strict_args with
                   | FStar_Pervasives_Native.None  ->
                       let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____12782  ->
                                 fun stack1  ->
                                   match uu____12782 with
                                   | (a,aq) ->
                                       let uu____12794 =
                                         let uu____12795 =
                                           let uu____12802 =
                                             let uu____12803 =
                                               let uu____12835 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____12835, false)
                                                in
                                             Clos uu____12803  in
                                           (uu____12802, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____12795  in
                                       uu____12794 :: stack1) args)
                          in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____12903  ->
                             let uu____12904 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length args)
                                in
                             FStar_Util.print1 "\tPushed %s arguments\n"
                               uu____12904);
                        norm cfg env stack1 head1)
                   | FStar_Pervasives_Native.Some strict_args1 ->
                       let norm_args =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____12955  ->
                                 match uu____12955 with
                                 | (a,i) ->
                                     let uu____12966 = norm cfg env [] a  in
                                     (uu____12966, i)))
                          in
                       let norm_args_len = FStar_List.length norm_args  in
                       let uu____12972 =
                         FStar_All.pipe_right strict_args1
                           (FStar_List.for_all
                              (fun i  ->
                                 if i >= norm_args_len
                                 then false
                                 else
                                   (let uu____12987 =
                                      FStar_List.nth norm_args i  in
                                    match uu____12987 with
                                    | (arg_i,uu____12998) ->
                                        let uu____12999 =
                                          FStar_Syntax_Util.head_and_args
                                            arg_i
                                           in
                                        (match uu____12999 with
                                         | (head2,uu____13018) ->
                                             let uu____13043 =
                                               let uu____13044 =
                                                 FStar_Syntax_Util.un_uinst
                                                   head2
                                                  in
                                               uu____13044.FStar_Syntax_Syntax.n
                                                in
                                             (match uu____13043 with
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____13048 -> true
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv ->
                                                  let uu____13051 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Env.is_datacon
                                                    cfg.FStar_TypeChecker_Cfg.tcenv
                                                    uu____13051
                                              | uu____13052 -> false)))))
                          in
                       if uu____12972
                       then
                         let stack1 =
                           FStar_All.pipe_right stack
                             (FStar_List.fold_right
                                (fun uu____13069  ->
                                   fun stack1  ->
                                     match uu____13069 with
                                     | (a,aq) ->
                                         let uu____13081 =
                                           let uu____13082 =
                                             let uu____13089 =
                                               let uu____13090 =
                                                 let uu____13122 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], a))
                                                    in
                                                 (env, a, uu____13122, false)
                                                  in
                                               Clos uu____13090  in
                                             (uu____13089, aq,
                                               (t1.FStar_Syntax_Syntax.pos))
                                              in
                                           Arg uu____13082  in
                                         uu____13081 :: stack1) norm_args)
                            in
                         (FStar_TypeChecker_Cfg.log cfg
                            (fun uu____13204  ->
                               let uu____13205 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length args)
                                  in
                               FStar_Util.print1 "\tPushed %s arguments\n"
                                 uu____13205);
                          norm cfg env stack1 head1)
                       else
                         (let head2 = closure_as_term cfg env head1  in
                          let term =
                            FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                              FStar_Pervasives_Native.None
                              t1.FStar_Syntax_Syntax.pos
                             in
                          rebuild cfg env stack term))
              | FStar_Syntax_Syntax.Tm_refine (x,uu____13225) when
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
                                ((let uu___1647_13270 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1647_13270.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1647_13270.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t_x
                                  }), f)) t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild cfg env stack t2
                     | uu____13271 ->
                         let uu____13286 = closure_as_term cfg env t1  in
                         rebuild cfg env stack uu____13286)
                  else
                    (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                     let uu____13290 =
                       FStar_Syntax_Subst.open_term
                         [(x, FStar_Pervasives_Native.None)] f
                        in
                     match uu____13290 with
                     | (closing,f1) ->
                         let f2 = norm cfg (dummy :: env) [] f1  in
                         let t2 =
                           let uu____13321 =
                             let uu____13322 =
                               let uu____13329 =
                                 FStar_Syntax_Subst.close closing f2  in
                               ((let uu___1656_13335 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1656_13335.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1656_13335.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t_x
                                 }), uu____13329)
                                in
                             FStar_Syntax_Syntax.Tm_refine uu____13322  in
                           mk uu____13321 t1.FStar_Syntax_Syntax.pos  in
                         rebuild cfg env stack t2)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                  then
                    let uu____13359 = closure_as_term cfg env t1  in
                    rebuild cfg env stack uu____13359
                  else
                    (let uu____13362 = FStar_Syntax_Subst.open_comp bs c  in
                     match uu____13362 with
                     | (bs1,c1) ->
                         let c2 =
                           let uu____13370 =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13396  -> dummy :: env1) env)
                              in
                           norm_comp cfg uu____13370 c1  in
                         let t2 =
                           let uu____13420 = norm_binders cfg env bs1  in
                           FStar_Syntax_Util.arrow uu____13420 c2  in
                         rebuild cfg env stack t2)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
                  -> norm cfg env stack t11
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
                  (match stack with
                   | (Match uu____13533)::uu____13534 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13547  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (Arg uu____13549)::uu____13550 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13561  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (App
                       (uu____13563,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_reify );
                                      FStar_Syntax_Syntax.pos = uu____13564;
                                      FStar_Syntax_Syntax.vars = uu____13565;_},uu____13566,uu____13567))::uu____13568
                       when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13575  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (MemoLazy uu____13577)::uu____13578 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13589  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | uu____13591 ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13594  ->
                             FStar_Util.print_string
                               "+++ Keeping ascription \n");
                        (let t12 = norm cfg env [] t11  in
                         FStar_TypeChecker_Cfg.log cfg
                           (fun uu____13599  ->
                              FStar_Util.print_string
                                "+++ Normalizing ascription \n");
                         (let tc1 =
                            match tc with
                            | FStar_Util.Inl t2 ->
                                let uu____13625 = norm cfg env [] t2  in
                                FStar_Util.Inl uu____13625
                            | FStar_Util.Inr c ->
                                let uu____13639 = norm_comp cfg env c  in
                                FStar_Util.Inr uu____13639
                             in
                          let tacopt1 =
                            FStar_Util.map_opt tacopt (norm cfg env [])  in
                          match stack with
                          | (Cfg cfg1)::stack1 ->
                              let t2 =
                                let uu____13662 =
                                  let uu____13663 =
                                    let uu____13690 =
                                      FStar_Syntax_Util.unascribe t12  in
                                    (uu____13690, (tc1, tacopt1), l)  in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____13663
                                   in
                                mk uu____13662 t1.FStar_Syntax_Syntax.pos  in
                              norm cfg1 env stack1 t2
                          | uu____13725 ->
                              let uu____13726 =
                                let uu____13727 =
                                  let uu____13728 =
                                    let uu____13755 =
                                      FStar_Syntax_Util.unascribe t12  in
                                    (uu____13755, (tc1, tacopt1), l)  in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____13728
                                   in
                                mk uu____13727 t1.FStar_Syntax_Syntax.pos  in
                              rebuild cfg env stack uu____13726))))
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
                      let uu___1735_13833 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (let uu___1737_13836 =
                             cfg.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak = true;
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1737_13836.FStar_TypeChecker_Cfg.for_extraction)
                           });
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1735_13833.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1735_13833.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___1735_13833.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1735_13833.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1735_13833.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1735_13833.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___1735_13833.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___1735_13833.FStar_TypeChecker_Cfg.reifying)
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
                            let uu____13877 =
                              FStar_Syntax_Subst.univ_var_opening
                                lb.FStar_Syntax_Syntax.lbunivs
                               in
                            match uu____13877 with
                            | (openings,lbunivs) ->
                                let cfg1 =
                                  let uu___1750_13897 = cfg  in
                                  let uu____13898 =
                                    FStar_TypeChecker_Env.push_univ_vars
                                      cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                     in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1750_13897.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv = uu____13898;
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1750_13897.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1750_13897.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1750_13897.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong =
                                      (uu___1750_13897.FStar_TypeChecker_Cfg.strong);
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1750_13897.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1750_13897.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1750_13897.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                let norm1 t2 =
                                  let uu____13905 =
                                    let uu____13906 =
                                      FStar_Syntax_Subst.subst openings t2
                                       in
                                    norm cfg1 env [] uu____13906  in
                                  FStar_Syntax_Subst.close_univ_vars lbunivs
                                    uu____13905
                                   in
                                let lbtyp =
                                  norm1 lb.FStar_Syntax_Syntax.lbtyp  in
                                let lbdef =
                                  norm1 lb.FStar_Syntax_Syntax.lbdef  in
                                let uu___1757_13909 = lb  in
                                {
                                  FStar_Syntax_Syntax.lbname =
                                    (uu___1757_13909.FStar_Syntax_Syntax.lbname);
                                  FStar_Syntax_Syntax.lbunivs = lbunivs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1757_13909.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = lbdef;
                                  FStar_Syntax_Syntax.lbattrs =
                                    (uu___1757_13909.FStar_Syntax_Syntax.lbattrs);
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1757_13909.FStar_Syntax_Syntax.lbpos)
                                }))
                     in
                  let uu____13910 =
                    mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                      t1.FStar_Syntax_Syntax.pos
                     in
                  rebuild cfg env stack uu____13910
              | FStar_Syntax_Syntax.Tm_let
                  ((uu____13923,{
                                  FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                    uu____13924;
                                  FStar_Syntax_Syntax.lbunivs = uu____13925;
                                  FStar_Syntax_Syntax.lbtyp = uu____13926;
                                  FStar_Syntax_Syntax.lbeff = uu____13927;
                                  FStar_Syntax_Syntax.lbdef = uu____13928;
                                  FStar_Syntax_Syntax.lbattrs = uu____13929;
                                  FStar_Syntax_Syntax.lbpos = uu____13930;_}::uu____13931),uu____13932)
                  -> rebuild cfg env stack t1
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let uu____13977 =
                    FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
                  if uu____13977
                  then
                    let binder =
                      let uu____13981 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.mk_binder uu____13981  in
                    let env1 =
                      let uu____13991 =
                        let uu____13998 =
                          let uu____13999 =
                            let uu____14031 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env, (lb.FStar_Syntax_Syntax.lbdef),
                              uu____14031, false)
                             in
                          Clos uu____13999  in
                        ((FStar_Pervasives_Native.Some binder), uu____13998)
                         in
                      uu____13991 :: env  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____14106  ->
                          FStar_Util.print_string "+++ Reducing Tm_let\n");
                     norm cfg env1 stack body)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____14113  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____14115 = closure_as_term cfg env t1  in
                        rebuild cfg env stack uu____14115))
                    else
                      (let uu____14118 =
                         let uu____14123 =
                           let uu____14124 =
                             let uu____14131 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____14131
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____14124]  in
                         FStar_Syntax_Subst.open_term uu____14123 body  in
                       match uu____14118 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____14158  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____14167 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____14167  in
                               FStar_Util.Inl
                                 (let uu___1798_14183 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1798_14183.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1798_14183.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____14186  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1803_14189 = lb  in
                                let uu____14190 =
                                  norm cfg env []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____14193 =
                                  FStar_List.map (norm cfg env [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1803_14189.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1803_14189.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____14190;
                                  FStar_Syntax_Syntax.lbattrs = uu____14193;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1803_14189.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____14228  -> dummy :: env1)
                                     env)
                                 in
                              let stack1 = (Cfg cfg) :: stack  in
                              let cfg1 =
                                let uu___1810_14253 = cfg  in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1810_14253.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1810_14253.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1810_14253.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1810_14253.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1810_14253.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1810_14253.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1810_14253.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1810_14253.FStar_TypeChecker_Cfg.reifying)
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____14257  ->
                                   FStar_Util.print_string
                                     "+++ Normalizing Tm_let -- body\n");
                              norm cfg1 env'
                                ((Let
                                    (env, bs, lb1,
                                      (t1.FStar_Syntax_Syntax.pos))) ::
                                stack1) body1))))
              | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                    ||
                    ((Prims.op_Negation
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                       &&
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations)
                  ->
                  let uu____14278 = FStar_Syntax_Subst.open_let_rec lbs body
                     in
                  (match uu____14278 with
                   | (lbs1,body1) ->
                       let lbs2 =
                         FStar_List.map
                           (fun lb  ->
                              let ty =
                                norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                 in
                              let lbname =
                                let uu____14314 =
                                  let uu___1826_14315 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1826_14315.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1826_14315.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  }  in
                                FStar_Util.Inl uu____14314  in
                              let uu____14316 =
                                FStar_Syntax_Util.abs_formals
                                  lb.FStar_Syntax_Syntax.lbdef
                                 in
                              match uu____14316 with
                              | (xs,def_body,lopt) ->
                                  let xs1 = norm_binders cfg env xs  in
                                  let env1 =
                                    let uu____14342 =
                                      FStar_List.map
                                        (fun uu____14364  -> dummy) xs1
                                       in
                                    let uu____14371 =
                                      let uu____14380 =
                                        FStar_List.map
                                          (fun uu____14396  -> dummy) lbs1
                                         in
                                      FStar_List.append uu____14380 env  in
                                    FStar_List.append uu____14342 uu____14371
                                     in
                                  let def_body1 = norm cfg env1 [] def_body
                                     in
                                  let lopt1 =
                                    match lopt with
                                    | FStar_Pervasives_Native.Some rc ->
                                        let uu____14416 =
                                          let uu___1840_14417 = rc  in
                                          let uu____14418 =
                                            FStar_Util.map_opt
                                              rc.FStar_Syntax_Syntax.residual_typ
                                              (norm cfg env1 [])
                                             in
                                          {
                                            FStar_Syntax_Syntax.residual_effect
                                              =
                                              (uu___1840_14417.FStar_Syntax_Syntax.residual_effect);
                                            FStar_Syntax_Syntax.residual_typ
                                              = uu____14418;
                                            FStar_Syntax_Syntax.residual_flags
                                              =
                                              (uu___1840_14417.FStar_Syntax_Syntax.residual_flags)
                                          }  in
                                        FStar_Pervasives_Native.Some
                                          uu____14416
                                    | uu____14427 -> lopt  in
                                  let def =
                                    FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                     in
                                  let uu___1845_14433 = lb  in
                                  {
                                    FStar_Syntax_Syntax.lbname = lbname;
                                    FStar_Syntax_Syntax.lbunivs =
                                      (uu___1845_14433.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp = ty;
                                    FStar_Syntax_Syntax.lbeff =
                                      (uu___1845_14433.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs =
                                      (uu___1845_14433.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (uu___1845_14433.FStar_Syntax_Syntax.lbpos)
                                  }) lbs1
                          in
                       let env' =
                         let uu____14443 =
                           FStar_List.map (fun uu____14459  -> dummy) lbs2
                            in
                         FStar_List.append uu____14443 env  in
                       let body2 = norm cfg env' [] body1  in
                       let uu____14467 =
                         FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                       (match uu____14467 with
                        | (lbs3,body3) ->
                            let t2 =
                              let uu___1854_14483 = t1  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_let
                                     ((true, lbs3), body3));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1854_14483.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1854_14483.FStar_Syntax_Syntax.vars)
                              }  in
                            rebuild cfg env stack t2))
              | FStar_Syntax_Syntax.Tm_let (lbs,body) when
                  Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                  ->
                  let uu____14517 = closure_as_term cfg env t1  in
                  rebuild cfg env stack uu____14517
              | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
                  let uu____14538 =
                    FStar_List.fold_right
                      (fun lb  ->
                         fun uu____14616  ->
                           match uu____14616 with
                           | (rec_env,memos,i) ->
                               let bv =
                                 let uu___1870_14741 =
                                   FStar_Util.left
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1870_14741.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index = i;
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1870_14741.FStar_Syntax_Syntax.sort)
                                 }  in
                               let f_i = FStar_Syntax_Syntax.bv_to_tm bv  in
                               let fix_f_i =
                                 mk (FStar_Syntax_Syntax.Tm_let (lbs, f_i))
                                   t1.FStar_Syntax_Syntax.pos
                                  in
                               let memo =
                                 FStar_Util.mk_ref
                                   FStar_Pervasives_Native.None
                                  in
                               let rec_env1 =
                                 (FStar_Pervasives_Native.None,
                                   (Clos (env, fix_f_i, memo, true)))
                                 :: rec_env  in
                               (rec_env1, (memo :: memos),
                                 (i + Prims.int_one)))
                      (FStar_Pervasives_Native.snd lbs)
                      (env, [], Prims.int_zero)
                     in
                  (match uu____14538 with
                   | (rec_env,memos,uu____14932) ->
                       let uu____14987 =
                         FStar_List.map2
                           (fun lb  ->
                              fun memo  ->
                                FStar_ST.op_Colon_Equals memo
                                  (FStar_Pervasives_Native.Some
                                     (rec_env,
                                       (lb.FStar_Syntax_Syntax.lbdef))))
                           (FStar_Pervasives_Native.snd lbs) memos
                          in
                       let body_env =
                         FStar_List.fold_right
                           (fun lb  ->
                              fun env1  ->
                                let uu____15236 =
                                  let uu____15243 =
                                    let uu____15244 =
                                      let uu____15276 =
                                        FStar_Util.mk_ref
                                          FStar_Pervasives_Native.None
                                         in
                                      (rec_env,
                                        (lb.FStar_Syntax_Syntax.lbdef),
                                        uu____15276, false)
                                       in
                                    Clos uu____15244  in
                                  (FStar_Pervasives_Native.None, uu____15243)
                                   in
                                uu____15236 :: env1)
                           (FStar_Pervasives_Native.snd lbs) env
                          in
                       norm cfg body_env stack body)
              | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____15361  ->
                        let uu____15362 =
                          FStar_Syntax_Print.metadata_to_string m  in
                        FStar_Util.print1 ">> metadata = %s\n" uu____15362);
                   (match m with
                    | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                        reduce_impure_comp cfg env stack head1
                          (FStar_Util.Inl m1) t2
                    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                        reduce_impure_comp cfg env stack head1
                          (FStar_Util.Inr (m1, m')) t2
                    | uu____15386 ->
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                        then norm cfg env stack head1
                        else
                          (match stack with
                           | uu____15390::uu____15391 ->
                               (match m with
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (l,r,uu____15396) ->
                                    norm cfg env ((Meta (env, m, r)) ::
                                      stack) head1
                                | FStar_Syntax_Syntax.Meta_pattern
                                    (names1,args) ->
                                    let args1 =
                                      norm_pattern_args cfg env args  in
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
                                | uu____15475 -> norm cfg env stack head1)
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
                                     let uu____15523 =
                                       let uu____15544 =
                                         norm_pattern_args cfg env args  in
                                       (names2, uu____15544)  in
                                     FStar_Syntax_Syntax.Meta_pattern
                                       uu____15523
                                 | uu____15573 -> m  in
                               let t2 =
                                 mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                   t1.FStar_Syntax_Syntax.pos
                                  in
                               rebuild cfg env stack t2)))
              | FStar_Syntax_Syntax.Tm_delayed uu____15579 ->
                  let t2 = FStar_Syntax_Subst.compress t1  in
                  norm cfg env stack t2
              | FStar_Syntax_Syntax.Tm_uvar uu____15603 ->
                  let t2 = FStar_Syntax_Subst.compress t1  in
                  (match t2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar uu____15617 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                       then
                         let uu____15631 =
                           let uu____15633 =
                             FStar_Range.string_of_range
                               t2.FStar_Syntax_Syntax.pos
                              in
                           let uu____15635 =
                             FStar_Syntax_Print.term_to_string t2  in
                           FStar_Util.format2
                             "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                             uu____15633 uu____15635
                            in
                         failwith uu____15631
                       else
                         (let uu____15640 = inline_closure_env cfg env [] t2
                             in
                          rebuild cfg env stack uu____15640)
                   | uu____15641 -> norm cfg env stack t2)))

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
              let uu____15650 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____15650 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____15664  ->
                        let uu____15665 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____15665);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____15678  ->
                        let uu____15679 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____15681 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____15679 uu____15681);
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
                      | (UnivArgs (us',uu____15694))::stack1 ->
                          ((let uu____15703 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____15703
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____15711 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____15711) us'
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
                      | uu____15747 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____15750 ->
                          let uu____15753 =
                            let uu____15755 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____15755
                             in
                          failwith uu____15753
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
              let stack1 = (Cfg cfg) :: stack  in
              let cfg1 =
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
                  let uu___1982_15783 = cfg  in
                  let uu____15784 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____15784;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1982_15783.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1982_15783.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1982_15783.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1982_15783.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1982_15783.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1982_15783.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1982_15783.FStar_TypeChecker_Cfg.reifying)
                  }
                else cfg  in
              let metadata =
                match m with
                | FStar_Util.Inl m1 ->
                    FStar_Syntax_Syntax.Meta_monadic (m1, t1)
                | FStar_Util.Inr (m1,m') ->
                    FStar_Syntax_Syntax.Meta_monadic_lift (m1, m', t1)
                 in
              norm cfg1 env
                ((Meta (env, metadata, (head1.FStar_Syntax_Syntax.pos))) ::
                stack1) head1

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
          fun head1  ->
            fun m  ->
              fun t  ->
                (match stack with
                 | (App
                     (uu____15815,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____15816;
                                    FStar_Syntax_Syntax.vars = uu____15817;_},uu____15818,uu____15819))::uu____15820
                     -> ()
                 | uu____15825 ->
                     let uu____15828 =
                       let uu____15830 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____15830
                        in
                     failwith uu____15828);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____15839  ->
                      let uu____15840 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____15842 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____15840
                        uu____15842);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____15846 =
                    let uu____15847 = FStar_Syntax_Subst.compress head3  in
                    uu____15847.FStar_Syntax_Syntax.n  in
                  match uu____15846 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____15868 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____15868
                         in
                      let uu____15869 =
                        let uu____15878 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_bind_repr
                           in
                        FStar_All.pipe_right uu____15878 FStar_Util.must  in
                      (match uu____15869 with
                       | (uu____15893,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____15903 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____15914 =
                                    let uu____15915 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____15915.FStar_Syntax_Syntax.n  in
                                  match uu____15914 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____15921,uu____15922))
                                      ->
                                      let uu____15931 =
                                        let uu____15932 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____15932.FStar_Syntax_Syntax.n  in
                                      (match uu____15931 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____15938,msrc,uu____15940))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____15949 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____15949
                                       | uu____15950 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____15951 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____15952 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____15952 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___2054_15957 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___2054_15957.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___2054_15957.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___2054_15957.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___2054_15957.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___2054_15957.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____15958 = FStar_List.tl stack
                                        in
                                     let uu____15959 =
                                       let uu____15960 =
                                         let uu____15967 =
                                           let uu____15968 =
                                             let uu____15982 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____15982)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____15968
                                            in
                                         FStar_Syntax_Syntax.mk uu____15967
                                          in
                                       uu____15960
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____15958 uu____15959
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____15998 =
                                       let uu____16000 = is_return body  in
                                       match uu____16000 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____16005;
                                             FStar_Syntax_Syntax.vars =
                                               uu____16006;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____16009 -> false  in
                                     if uu____15998
                                     then
                                       norm cfg env stack
                                         lb.FStar_Syntax_Syntax.lbdef
                                     else
                                       (let rng =
                                          head3.FStar_Syntax_Syntax.pos  in
                                        let head4 =
                                          FStar_All.pipe_left
                                            FStar_Syntax_Util.mk_reify
                                            lb.FStar_Syntax_Syntax.lbdef
                                           in
                                        let body1 =
                                          FStar_All.pipe_left
                                            FStar_Syntax_Util.mk_reify body
                                           in
                                        let body_rc =
                                          {
                                            FStar_Syntax_Syntax.residual_effect
                                              = m;
                                            FStar_Syntax_Syntax.residual_typ
                                              =
                                              (FStar_Pervasives_Native.Some t);
                                            FStar_Syntax_Syntax.residual_flags
                                              = []
                                          }  in
                                        let body2 =
                                          let uu____16033 =
                                            let uu____16040 =
                                              let uu____16041 =
                                                let uu____16060 =
                                                  let uu____16069 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____16069]  in
                                                (uu____16060, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____16041
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____16040
                                             in
                                          uu____16033
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____16108 =
                                            let uu____16109 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____16109.FStar_Syntax_Syntax.n
                                             in
                                          match uu____16108 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____16115::uu____16116::[])
                                              ->
                                              let uu____16121 =
                                                let uu____16128 =
                                                  let uu____16129 =
                                                    let uu____16136 =
                                                      let uu____16137 =
                                                        let uu____16138 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____16138
                                                         in
                                                      let uu____16139 =
                                                        let uu____16142 =
                                                          let uu____16143 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____16143
                                                           in
                                                        [uu____16142]  in
                                                      uu____16137 ::
                                                        uu____16139
                                                       in
                                                    (bind1, uu____16136)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____16129
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____16128
                                                 in
                                              uu____16121
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____16146 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____16161 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____16161
                                          then
                                            let uu____16174 =
                                              let uu____16183 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____16183
                                               in
                                            let uu____16184 =
                                              let uu____16195 =
                                                let uu____16204 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____16204
                                                 in
                                              [uu____16195]  in
                                            uu____16174 :: uu____16184
                                          else []  in
                                        let reified =
                                          let args =
                                            let uu____16253 =
                                              FStar_Syntax_Util.is_layered ed
                                               in
                                            if uu____16253
                                            then
                                              let unit_args =
                                                let uu____16277 =
                                                  let uu____16278 =
                                                    let uu____16281 =
                                                      let uu____16282 =
                                                        FStar_All.pipe_right
                                                          ed
                                                          FStar_Syntax_Util.get_bind_vc_combinator
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____16282
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____16281
                                                      FStar_Syntax_Subst.compress
                                                     in
                                                  uu____16278.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____16277 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (uu____16323::uu____16324::bs,uu____16326)
                                                    when
                                                    (FStar_List.length bs) >=
                                                      (Prims.of_int (2))
                                                    ->
                                                    let uu____16378 =
                                                      let uu____16387 =
                                                        FStar_All.pipe_right
                                                          bs
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs)
                                                                -
                                                                (Prims.of_int (2))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____16387
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____16378
                                                      (FStar_List.map
                                                         (fun uu____16518  ->
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.unit_const))
                                                | uu____16525 ->
                                                    let uu____16526 =
                                                      let uu____16532 =
                                                        let uu____16534 =
                                                          FStar_Ident.string_of_lid
                                                            ed.FStar_Syntax_Syntax.mname
                                                           in
                                                        let uu____16536 =
                                                          let uu____16538 =
                                                            let uu____16539 =
                                                              FStar_All.pipe_right
                                                                ed
                                                                FStar_Syntax_Util.get_bind_vc_combinator
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____16539
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____16538
                                                            FStar_Syntax_Print.term_to_string
                                                           in
                                                        FStar_Util.format2
                                                          "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                          uu____16534
                                                          uu____16536
                                                         in
                                                      (FStar_Errors.Fatal_UnexpectedEffect,
                                                        uu____16532)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____16526 rng
                                                 in
                                              let uu____16573 =
                                                FStar_Syntax_Syntax.as_arg
                                                  lb.FStar_Syntax_Syntax.lbtyp
                                                 in
                                              let uu____16582 =
                                                let uu____16593 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____16602 =
                                                  let uu____16613 =
                                                    let uu____16624 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head4
                                                       in
                                                    let uu____16633 =
                                                      let uu____16644 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          body2
                                                         in
                                                      [uu____16644]  in
                                                    uu____16624 ::
                                                      uu____16633
                                                     in
                                                  FStar_List.append unit_args
                                                    uu____16613
                                                   in
                                                uu____16593 :: uu____16602
                                                 in
                                              uu____16573 :: uu____16582
                                            else
                                              (let uu____16703 =
                                                 let uu____16714 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____16723 =
                                                   let uu____16734 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   [uu____16734]  in
                                                 uu____16714 :: uu____16723
                                                  in
                                               let uu____16767 =
                                                 let uu____16778 =
                                                   let uu____16789 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       FStar_Syntax_Syntax.tun
                                                      in
                                                   let uu____16798 =
                                                     let uu____16809 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         head4
                                                        in
                                                     let uu____16818 =
                                                       let uu____16829 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let uu____16838 =
                                                         let uu____16849 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2
                                                            in
                                                         [uu____16849]  in
                                                       uu____16829 ::
                                                         uu____16838
                                                        in
                                                     uu____16809 ::
                                                       uu____16818
                                                      in
                                                   uu____16789 :: uu____16798
                                                    in
                                                 FStar_List.append
                                                   maybe_range_arg
                                                   uu____16778
                                                  in
                                               FStar_List.append uu____16703
                                                 uu____16767)
                                             in
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (bind_inst, args))
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____16930  ->
                                             let uu____16931 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____16933 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____16931 uu____16933);
                                        (let uu____16936 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____16936 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____16964 = FStar_Options.defensive ()  in
                        if uu____16964
                        then
                          let is_arg_impure uu____16979 =
                            match uu____16979 with
                            | (e,q) ->
                                let uu____16993 =
                                  let uu____16994 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16994.FStar_Syntax_Syntax.n  in
                                (match uu____16993 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____17010 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____17010
                                 | uu____17012 -> false)
                             in
                          let uu____17014 =
                            let uu____17016 =
                              let uu____17027 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____17027 :: args  in
                            FStar_Util.for_some is_arg_impure uu____17016  in
                          (if uu____17014
                           then
                             let uu____17053 =
                               let uu____17059 =
                                 let uu____17061 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____17061
                                  in
                               (FStar_Errors.Warning_Defensive, uu____17059)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____17053
                           else ())
                        else ());
                       (let fallback1 uu____17074 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____17078  ->
                               let uu____17079 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____17079 "");
                          (let uu____17083 = FStar_List.tl stack  in
                           let uu____17084 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____17083 uu____17084)
                           in
                        let fallback2 uu____17090 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____17094  ->
                               let uu____17095 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____17095 "");
                          (let uu____17099 = FStar_List.tl stack  in
                           let uu____17100 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____17099 uu____17100)
                           in
                        let uu____17105 =
                          let uu____17106 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____17106.FStar_Syntax_Syntax.n  in
                        match uu____17105 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____17112 =
                              let uu____17114 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____17114  in
                            if uu____17112
                            then fallback1 ()
                            else
                              (let uu____17119 =
                                 let uu____17121 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____17121  in
                               if uu____17119
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____17138 =
                                      let uu____17143 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____17143 args
                                       in
                                    uu____17138 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____17144 = FStar_List.tl stack  in
                                  norm cfg env uu____17144 t1))
                        | uu____17145 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____17147) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____17171 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____17171  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____17175  ->
                            let uu____17176 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____17176);
                       (let uu____17179 = FStar_List.tl stack  in
                        norm cfg env uu____17179 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____17300  ->
                                match uu____17300 with
                                | (pat,wopt,tm) ->
                                    let uu____17348 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____17348)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____17380 = FStar_List.tl stack  in
                      norm cfg env uu____17380 tm
                  | uu____17381 -> fallback ()))

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
              (fun uu____17395  ->
                 let uu____17396 = FStar_Ident.string_of_lid msrc  in
                 let uu____17398 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17400 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17396
                   uu____17398 uu____17400);
            (let uu____17403 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____17406 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env)
                     in
                  Prims.op_Negation uu____17406)
                in
             if uu____17403
             then
               let ed =
                 let uu____17411 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17411  in
               let uu____17412 =
                 let uu____17419 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr
                    in
                 FStar_All.pipe_right uu____17419 FStar_Util.must  in
               match uu____17412 with
               | (uu____17456,return_repr) ->
                   let return_inst =
                     let uu____17465 =
                       let uu____17466 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17466.FStar_Syntax_Syntax.n  in
                     match uu____17465 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17472::[]) ->
                         let uu____17477 =
                           let uu____17484 =
                             let uu____17485 =
                               let uu____17492 =
                                 let uu____17493 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17493]  in
                               (return_tm, uu____17492)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17485  in
                           FStar_Syntax_Syntax.mk uu____17484  in
                         uu____17477 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17496 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17500 =
                     let uu____17507 =
                       let uu____17508 =
                         let uu____17525 =
                           let uu____17536 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17545 =
                             let uu____17556 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17556]  in
                           uu____17536 :: uu____17545  in
                         (return_inst, uu____17525)  in
                       FStar_Syntax_Syntax.Tm_app uu____17508  in
                     FStar_Syntax_Syntax.mk uu____17507  in
                   uu____17500 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17603 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17603 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17606 =
                      let uu____17608 = FStar_Ident.text_of_lid msrc  in
                      let uu____17610 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17608 uu____17610
                       in
                    failwith uu____17606
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17613;
                      FStar_TypeChecker_Env.mtarget = uu____17614;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17615;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17635 =
                      let uu____17637 = FStar_Ident.text_of_lid msrc  in
                      let uu____17639 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17637 uu____17639
                       in
                    failwith uu____17635
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17642;
                      FStar_TypeChecker_Env.mtarget = uu____17643;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17644;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____17675 =
                        FStar_TypeChecker_Env.is_reifiable_effect env msrc
                         in
                      if uu____17675
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____17680 =
                           let uu____17687 =
                             let uu____17688 =
                               let uu____17707 =
                                 let uu____17716 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____17716]  in
                               (uu____17707, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____17688  in
                           FStar_Syntax_Syntax.mk uu____17687  in
                         uu____17680 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____17749 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    lift uu____17749 t e1))

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
                (fun uu____17819  ->
                   match uu____17819 with
                   | (a,imp) ->
                       let uu____17838 = norm cfg env [] a  in
                       (uu____17838, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17848  ->
             let uu____17849 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17851 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17849 uu____17851);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17877 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17880  -> FStar_Pervasives_Native.Some _17880)
                     uu____17877
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2219_17881 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2219_17881.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2219_17881.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17903 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17906  -> FStar_Pervasives_Native.Some _17906)
                     uu____17903
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2230_17907 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2230_17907.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2230_17907.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17952  ->
                      match uu____17952 with
                      | (a,i) ->
                          let uu____17972 = norm cfg env [] a  in
                          (uu____17972, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17994  ->
                       match uu___14_17994 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17998 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17998
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2247_18006 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2249_18009 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2249_18009.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2247_18006.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2247_18006.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____18013 = b  in
        match uu____18013 with
        | (x,imp) ->
            let x1 =
              let uu___2257_18021 = x  in
              let uu____18022 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2257_18021.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2257_18021.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____18022
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____18033 =
                    let uu____18034 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____18034  in
                  FStar_Pervasives_Native.Some uu____18033
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____18045 =
          FStar_List.fold_left
            (fun uu____18079  ->
               fun b  ->
                 match uu____18079 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____18045 with | (nbs,uu____18159) -> FStar_List.rev nbs

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
            let uu____18191 =
              let uu___2282_18192 = rc  in
              let uu____18193 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2282_18192.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____18193;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2282_18192.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____18191
        | uu____18211 -> lopt

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
            (let uu____18221 = FStar_Syntax_Print.term_to_string tm  in
             let uu____18223 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____18221 uu____18223)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_18235  ->
      match uu___15_18235 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____18248 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____18248 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____18252 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____18252)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____18260 = norm_cb cfg  in
            reduce_primops uu____18260 cfg env tm  in
          let uu____18265 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____18265
          then tm1
          else
            (let w t =
               let uu___2311_18284 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2311_18284.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2311_18284.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____18296 =
                 let uu____18297 = FStar_Syntax_Util.unmeta t  in
                 uu____18297.FStar_Syntax_Syntax.n  in
               match uu____18296 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____18309 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18373)::args1,(bv,uu____18376)::bs1) ->
                   let uu____18430 =
                     let uu____18431 = FStar_Syntax_Subst.compress t  in
                     uu____18431.FStar_Syntax_Syntax.n  in
                   (match uu____18430 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18436 -> false)
               | ([],[]) -> true
               | (uu____18467,uu____18468) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18519 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18521 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18519
                    uu____18521)
               else ();
               (let uu____18526 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18526 with
                | (hd1,args) ->
                    let uu____18565 =
                      let uu____18566 = FStar_Syntax_Subst.compress hd1  in
                      uu____18566.FStar_Syntax_Syntax.n  in
                    (match uu____18565 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____18574 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18576 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18578 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18574 uu____18576 uu____18578)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18583 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18601 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18603 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18601
                    uu____18603)
               else ();
               (let uu____18608 = FStar_Syntax_Util.is_squash t  in
                match uu____18608 with
                | FStar_Pervasives_Native.Some (uu____18619,t') ->
                    is_applied bs t'
                | uu____18631 ->
                    let uu____18640 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18640 with
                     | FStar_Pervasives_Native.Some (uu____18651,t') ->
                         is_applied bs t'
                     | uu____18663 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18687 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18687 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18694)::(q,uu____18696)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18739 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18741 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18739 uu____18741)
                    else ();
                    (let uu____18746 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18746 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18751 =
                           let uu____18752 = FStar_Syntax_Subst.compress p
                              in
                           uu____18752.FStar_Syntax_Syntax.n  in
                         (match uu____18751 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18763 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18763))
                          | uu____18766 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18769)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18794 =
                           let uu____18795 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18795.FStar_Syntax_Syntax.n  in
                         (match uu____18794 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18806 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18806))
                          | uu____18809 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18813 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18813 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18818 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18818 with
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
                                     let uu____18832 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18832))
                               | uu____18835 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18840)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18865 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18865 with
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
                                     let uu____18879 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18879))
                               | uu____18882 -> FStar_Pervasives_Native.None)
                          | uu____18885 -> FStar_Pervasives_Native.None)
                     | uu____18888 -> FStar_Pervasives_Native.None))
               | uu____18891 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18904 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18904 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18910)::[],uu____18911,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18931 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18933 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18931
                         uu____18933)
                    else ();
                    is_quantified_const bv phi')
               | uu____18938 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18953 =
                 let uu____18954 = FStar_Syntax_Subst.compress phi  in
                 uu____18954.FStar_Syntax_Syntax.n  in
               match uu____18953 with
               | FStar_Syntax_Syntax.Tm_match (uu____18960,br::brs) ->
                   let uu____19027 = br  in
                   (match uu____19027 with
                    | (uu____19045,uu____19046,e) ->
                        let r =
                          let uu____19068 = simp_t e  in
                          match uu____19068 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____19080 =
                                FStar_List.for_all
                                  (fun uu____19099  ->
                                     match uu____19099 with
                                     | (uu____19113,uu____19114,e') ->
                                         let uu____19128 = simp_t e'  in
                                         uu____19128 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____19080
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____19144 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____19154 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____19154
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____19192 =
                 match uu____19192 with
                 | (t1,q) ->
                     let uu____19213 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____19213 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____19245 -> (t1, q))
                  in
               let uu____19258 = FStar_Syntax_Util.head_and_args t  in
               match uu____19258 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____19338 =
                 let uu____19339 = FStar_Syntax_Util.unmeta ty  in
                 uu____19339.FStar_Syntax_Syntax.n  in
               match uu____19338 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____19344) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____19349,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____19373 -> false  in
             let simplify1 arg =
               let uu____19406 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____19406, arg)  in
             let uu____19421 = is_forall_const tm1  in
             match uu____19421 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____19427 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____19429 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____19427
                       uu____19429)
                  else ();
                  (let uu____19434 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____19434))
             | FStar_Pervasives_Native.None  ->
                 let uu____19435 =
                   let uu____19436 = FStar_Syntax_Subst.compress tm1  in
                   uu____19436.FStar_Syntax_Syntax.n  in
                 (match uu____19435 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19440;
                              FStar_Syntax_Syntax.vars = uu____19441;_},uu____19442);
                         FStar_Syntax_Syntax.pos = uu____19443;
                         FStar_Syntax_Syntax.vars = uu____19444;_},args)
                      ->
                      let uu____19474 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19474
                      then
                        let uu____19477 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19477 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19535)::
                             (uu____19536,(arg,uu____19538))::[] ->
                             maybe_auto_squash arg
                         | (uu____19611,(arg,uu____19613))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19614)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19687)::uu____19688::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19758::(FStar_Pervasives_Native.Some (false
                                         ),uu____19759)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19829 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19847 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19847
                         then
                           let uu____19850 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19850 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19908)::uu____19909::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19979::(FStar_Pervasives_Native.Some (true
                                           ),uu____19980)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20050)::(uu____20051,(arg,uu____20053))::[]
                               -> maybe_auto_squash arg
                           | (uu____20126,(arg,uu____20128))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20129)::[]
                               -> maybe_auto_squash arg
                           | uu____20202 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20220 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20220
                            then
                              let uu____20223 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20223 with
                              | uu____20281::(FStar_Pervasives_Native.Some
                                              (true ),uu____20282)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20352)::uu____20353::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20423)::(uu____20424,(arg,uu____20426))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20499,(p,uu____20501))::(uu____20502,
                                                                (q,uu____20504))::[]
                                  ->
                                  let uu____20576 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20576
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20581 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20599 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20599
                               then
                                 let uu____20602 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20602 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20660)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20661)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20735)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20736)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20810)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20811)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20885)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20886)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20960,(arg,uu____20962))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20963)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21036)::(uu____21037,(arg,uu____21039))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21112,(arg,uu____21114))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21115)::[]
                                     ->
                                     let uu____21188 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21188
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21189)::(uu____21190,(arg,uu____21192))::[]
                                     ->
                                     let uu____21265 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21265
                                 | (uu____21266,(p,uu____21268))::(uu____21269,
                                                                   (q,uu____21271))::[]
                                     ->
                                     let uu____21343 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21343
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21348 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21366 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21366
                                  then
                                    let uu____21369 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21369 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21427)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21471)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21515 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21533 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21533
                                     then
                                       match args with
                                       | (t,uu____21537)::[] ->
                                           let uu____21562 =
                                             let uu____21563 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21563.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21562 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21566::[],body,uu____21568)
                                                ->
                                                let uu____21603 = simp_t body
                                                   in
                                                (match uu____21603 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21609 -> tm1)
                                            | uu____21613 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21615))::(t,uu____21617)::[]
                                           ->
                                           let uu____21657 =
                                             let uu____21658 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21658.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21657 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21661::[],body,uu____21663)
                                                ->
                                                let uu____21698 = simp_t body
                                                   in
                                                (match uu____21698 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21706 -> tm1)
                                            | uu____21710 -> tm1)
                                       | uu____21711 -> tm1
                                     else
                                       (let uu____21724 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21724
                                        then
                                          match args with
                                          | (t,uu____21728)::[] ->
                                              let uu____21753 =
                                                let uu____21754 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21754.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21753 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21757::[],body,uu____21759)
                                                   ->
                                                   let uu____21794 =
                                                     simp_t body  in
                                                   (match uu____21794 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21800 -> tm1)
                                               | uu____21804 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21806))::(t,uu____21808)::[]
                                              ->
                                              let uu____21848 =
                                                let uu____21849 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21849.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21848 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21852::[],body,uu____21854)
                                                   ->
                                                   let uu____21889 =
                                                     simp_t body  in
                                                   (match uu____21889 with
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
                                                    | uu____21897 -> tm1)
                                               | uu____21901 -> tm1)
                                          | uu____21902 -> tm1
                                        else
                                          (let uu____21915 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21915
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21918;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21919;_},uu____21920)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21946;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21947;_},uu____21948)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21974 -> tm1
                                           else
                                             (let uu____21987 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____21987
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____22001 =
                                                    let uu____22002 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____22002.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____22001 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____22013 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____22027 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____22027
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____22066 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____22066
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____22072 =
                                                         let uu____22073 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____22073.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____22072 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____22076 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____22084 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____22084
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____22093
                                                                  =
                                                                  let uu____22094
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____22094.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____22093
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____22100)
                                                                    -> hd1
                                                                | uu____22125
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____22129
                                                                =
                                                                let uu____22140
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____22140]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____22129)
                                                       | uu____22173 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____22178 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____22178 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____22198 ->
                                                     let uu____22207 =
                                                       let uu____22214 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____22214 cfg env
                                                        in
                                                     uu____22207 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____22220;
                         FStar_Syntax_Syntax.vars = uu____22221;_},args)
                      ->
                      let uu____22247 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22247
                      then
                        let uu____22250 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22250 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22308)::
                             (uu____22309,(arg,uu____22311))::[] ->
                             maybe_auto_squash arg
                         | (uu____22384,(arg,uu____22386))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22387)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22460)::uu____22461::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22531::(FStar_Pervasives_Native.Some (false
                                         ),uu____22532)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22602 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22620 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22620
                         then
                           let uu____22623 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22623 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22681)::uu____22682::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22752::(FStar_Pervasives_Native.Some (true
                                           ),uu____22753)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22823)::(uu____22824,(arg,uu____22826))::[]
                               -> maybe_auto_squash arg
                           | (uu____22899,(arg,uu____22901))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22902)::[]
                               -> maybe_auto_squash arg
                           | uu____22975 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22993 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22993
                            then
                              let uu____22996 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____22996 with
                              | uu____23054::(FStar_Pervasives_Native.Some
                                              (true ),uu____23055)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____23125)::uu____23126::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____23196)::(uu____23197,(arg,uu____23199))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23272,(p,uu____23274))::(uu____23275,
                                                                (q,uu____23277))::[]
                                  ->
                                  let uu____23349 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23349
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23354 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23372 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23372
                               then
                                 let uu____23375 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23375 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23433)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23434)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23508)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23509)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23583)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23584)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23658)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23659)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23733,(arg,uu____23735))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23736)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23809)::(uu____23810,(arg,uu____23812))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23885,(arg,uu____23887))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23888)::[]
                                     ->
                                     let uu____23961 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23961
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23962)::(uu____23963,(arg,uu____23965))::[]
                                     ->
                                     let uu____24038 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____24038
                                 | (uu____24039,(p,uu____24041))::(uu____24042,
                                                                   (q,uu____24044))::[]
                                     ->
                                     let uu____24116 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____24116
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____24121 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____24139 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____24139
                                  then
                                    let uu____24142 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____24142 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____24200)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____24244)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____24288 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____24306 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____24306
                                     then
                                       match args with
                                       | (t,uu____24310)::[] ->
                                           let uu____24335 =
                                             let uu____24336 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24336.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24335 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24339::[],body,uu____24341)
                                                ->
                                                let uu____24376 = simp_t body
                                                   in
                                                (match uu____24376 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24382 -> tm1)
                                            | uu____24386 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24388))::(t,uu____24390)::[]
                                           ->
                                           let uu____24430 =
                                             let uu____24431 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24431.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24430 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24434::[],body,uu____24436)
                                                ->
                                                let uu____24471 = simp_t body
                                                   in
                                                (match uu____24471 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24479 -> tm1)
                                            | uu____24483 -> tm1)
                                       | uu____24484 -> tm1
                                     else
                                       (let uu____24497 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24497
                                        then
                                          match args with
                                          | (t,uu____24501)::[] ->
                                              let uu____24526 =
                                                let uu____24527 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24527.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24526 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24530::[],body,uu____24532)
                                                   ->
                                                   let uu____24567 =
                                                     simp_t body  in
                                                   (match uu____24567 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24573 -> tm1)
                                               | uu____24577 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24579))::(t,uu____24581)::[]
                                              ->
                                              let uu____24621 =
                                                let uu____24622 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24622.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24621 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24625::[],body,uu____24627)
                                                   ->
                                                   let uu____24662 =
                                                     simp_t body  in
                                                   (match uu____24662 with
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
                                                    | uu____24670 -> tm1)
                                               | uu____24674 -> tm1)
                                          | uu____24675 -> tm1
                                        else
                                          (let uu____24688 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24688
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24691;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24692;_},uu____24693)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24719;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24720;_},uu____24721)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24747 -> tm1
                                           else
                                             (let uu____24760 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____24760
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____24774 =
                                                    let uu____24775 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____24775.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____24774 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____24786 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24800 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____24800
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____24835 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____24835
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24841 =
                                                         let uu____24842 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____24842.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____24841 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24845 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24853 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24853
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24862
                                                                  =
                                                                  let uu____24863
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24863.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24862
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____24869)
                                                                    -> hd1
                                                                | uu____24894
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____24898
                                                                =
                                                                let uu____24909
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____24909]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24898)
                                                       | uu____24942 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24947 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____24947 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24967 ->
                                                     let uu____24976 =
                                                       let uu____24983 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____24983 cfg env
                                                        in
                                                     uu____24976 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24994 = simp_t t  in
                      (match uu____24994 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____25003 ->
                      let uu____25026 = is_const_match tm1  in
                      (match uu____25026 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____25035 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____25045  ->
               (let uu____25047 = FStar_Syntax_Print.tag_of_term t  in
                let uu____25049 = FStar_Syntax_Print.term_to_string t  in
                let uu____25051 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____25059 =
                  let uu____25061 =
                    let uu____25064 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____25064
                     in
                  stack_to_string uu____25061  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____25047 uu____25049 uu____25051 uu____25059);
               (let uu____25089 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____25089
                then
                  let uu____25093 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____25093 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____25100 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____25102 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____25104 =
                          let uu____25106 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____25106
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____25100
                          uu____25102 uu____25104);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____25128 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____25136)::uu____25137 -> true
                | uu____25147 -> false)
              in
           if uu____25128
           then
             let uu____25150 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____25150 (norm cfg env stack)
           else
             (let t_opt = is_wp_req_ens_commutation cfg t  in
              let uu____25158 = FStar_All.pipe_right t_opt FStar_Util.is_some
                 in
              if uu____25158
              then
                ((let uu____25165 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         cfg.FStar_TypeChecker_Cfg.tcenv)
                      (FStar_Options.Other "WPReqEns")
                     in
                  if uu____25165
                  then
                    let uu____25170 = FStar_Syntax_Print.term_to_string t  in
                    let uu____25172 =
                      let uu____25174 =
                        FStar_All.pipe_right t_opt FStar_Util.must  in
                      FStar_All.pipe_right uu____25174
                        FStar_Syntax_Print.term_to_string
                       in
                    FStar_Util.print2
                      "In rebuild: reduced a wp req ens commutation from \n%s\n to \n%s"
                      uu____25170 uu____25172
                  else ());
                 (let uu____25181 =
                    FStar_All.pipe_right t_opt FStar_Util.must  in
                  FStar_All.pipe_right uu____25181 (norm cfg env stack)))
              else
                (let t1 = maybe_simplify cfg env stack t  in
                 match stack with
                 | [] -> t1
                 | (Debug (tm,time_then))::stack1 ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let time_now = FStar_Util.now ()  in
                         let uu____25195 =
                           let uu____25197 =
                             let uu____25199 =
                               FStar_Util.time_diff time_then time_now  in
                             FStar_Pervasives_Native.snd uu____25199  in
                           FStar_Util.string_of_int uu____25197  in
                         let uu____25206 =
                           FStar_Syntax_Print.term_to_string tm  in
                         let uu____25208 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                         let uu____25210 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print4
                           "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____25195 uu____25206 uu____25208 uu____25210)
                      else ();
                      rebuild cfg env stack1 t1)
                 | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
                 | (Meta (uu____25219,m,r))::stack1 ->
                     let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                     rebuild cfg env stack1 t2
                 | (MemoLazy r)::stack1 ->
                     (set_memo cfg r (env, t1);
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____25248  ->
                           let uu____25249 =
                             FStar_Syntax_Print.term_to_string t1  in
                           FStar_Util.print1 "\tSet memo %s\n" uu____25249);
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
                     let uu____25292 =
                       let uu___2944_25293 =
                         FStar_Syntax_Util.abs bs1 t1 lopt1  in
                       {
                         FStar_Syntax_Syntax.n =
                           (uu___2944_25293.FStar_Syntax_Syntax.n);
                         FStar_Syntax_Syntax.pos = r;
                         FStar_Syntax_Syntax.vars =
                           (uu___2944_25293.FStar_Syntax_Syntax.vars)
                       }  in
                     rebuild cfg env stack1 uu____25292
                 | (Arg
                     (Univ uu____25296,uu____25297,uu____25298))::uu____25299
                     -> failwith "Impossible"
                 | (Arg (Dummy ,uu____25303,uu____25304))::uu____25305 ->
                     failwith "Impossible"
                 | (UnivArgs (us,r))::stack1 ->
                     let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                     rebuild cfg env stack1 t2
                 | (Arg
                     (Clos (env_arg,tm,uu____25321,uu____25322),aq,r))::stack1
                     when
                     let uu____25374 = head_of t1  in
                     FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____25374
                     ->
                     let t2 =
                       let uu____25378 =
                         let uu____25383 =
                           let uu____25384 = closure_as_term cfg env_arg tm
                              in
                           (uu____25384, aq)  in
                         FStar_Syntax_Syntax.extend_app t1 uu____25383  in
                       uu____25378 FStar_Pervasives_Native.None r  in
                     rebuild cfg env stack1 t2
                 | (Arg (Clos (env_arg,tm,m,uu____25394),aq,r))::stack1 ->
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____25449  ->
                           let uu____25450 =
                             FStar_Syntax_Print.term_to_string tm  in
                           FStar_Util.print1 "Rebuilding with arg %s\n"
                             uu____25450);
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
                        (let uu____25470 = FStar_ST.op_Bang m  in
                         match uu____25470 with
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
                         | FStar_Pervasives_Native.Some (uu____25558,a) ->
                             let t2 =
                               FStar_Syntax_Syntax.extend_app t1 (a, aq)
                                 FStar_Pervasives_Native.None r
                                in
                             rebuild cfg env_arg stack1 t2))
                 | (App (env1,head1,aq,r))::stack' when
                     should_reify cfg stack ->
                     let t0 = t1  in
                     let fallback msg uu____25614 =
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____25619  ->
                            let uu____25620 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not reifying%s: %s\n" msg
                              uu____25620);
                       (let t2 =
                          FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                            FStar_Pervasives_Native.None r
                           in
                        rebuild cfg env1 stack' t2)
                        in
                     let uu____25630 =
                       let uu____25631 = FStar_Syntax_Subst.compress t1  in
                       uu____25631.FStar_Syntax_Syntax.n  in
                     (match uu____25630 with
                      | FStar_Syntax_Syntax.Tm_meta
                          (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                          do_reify_monadic (fallback " (1)") cfg env1 stack
                            t2 m ty
                      | FStar_Syntax_Syntax.Tm_meta
                          (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                           (msrc,mtgt,ty))
                          ->
                          let lifted =
                            let uu____25659 = closure_as_term cfg env1 ty  in
                            reify_lift cfg t2 msrc mtgt uu____25659  in
                          (FStar_TypeChecker_Cfg.log cfg
                             (fun uu____25663  ->
                                let uu____25664 =
                                  FStar_Syntax_Print.term_to_string lifted
                                   in
                                FStar_Util.print1 "Reified lift to (1): %s\n"
                                  uu____25664);
                           (let uu____25667 = FStar_List.tl stack  in
                            norm cfg env1 uu____25667 lifted))
                      | FStar_Syntax_Syntax.Tm_app
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reflect uu____25668);
                             FStar_Syntax_Syntax.pos = uu____25669;
                             FStar_Syntax_Syntax.vars = uu____25670;_},
                           (e,uu____25672)::[])
                          -> norm cfg env1 stack' e
                      | FStar_Syntax_Syntax.Tm_app uu____25711 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                          ->
                          let uu____25728 =
                            FStar_Syntax_Util.head_and_args t1  in
                          (match uu____25728 with
                           | (hd1,args) ->
                               let uu____25771 =
                                 let uu____25772 =
                                   FStar_Syntax_Util.un_uinst hd1  in
                                 uu____25772.FStar_Syntax_Syntax.n  in
                               (match uu____25771 with
                                | FStar_Syntax_Syntax.Tm_fvar fv ->
                                    let uu____25776 =
                                      FStar_TypeChecker_Cfg.find_prim_step
                                        cfg fv
                                       in
                                    (match uu____25776 with
                                     | FStar_Pervasives_Native.Some
                                         {
                                           FStar_TypeChecker_Cfg.name =
                                             uu____25779;
                                           FStar_TypeChecker_Cfg.arity =
                                             uu____25780;
                                           FStar_TypeChecker_Cfg.univ_arity =
                                             uu____25781;
                                           FStar_TypeChecker_Cfg.auto_reflect
                                             = FStar_Pervasives_Native.Some
                                             n1;
                                           FStar_TypeChecker_Cfg.strong_reduction_ok
                                             = uu____25783;
                                           FStar_TypeChecker_Cfg.requires_binder_substitution
                                             = uu____25784;
                                           FStar_TypeChecker_Cfg.interpretation
                                             = uu____25785;
                                           FStar_TypeChecker_Cfg.interpretation_nbe
                                             = uu____25786;_}
                                         when (FStar_List.length args) = n1
                                         -> norm cfg env1 stack' t1
                                     | uu____25822 -> fallback " (3)" ())
                                | uu____25826 -> fallback " (4)" ()))
                      | uu____25828 -> fallback " (2)" ())
                 | (App (env1,head1,aq,r))::stack1 ->
                     let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack1 t2
                 | (Match (env',branches,cfg1,r))::stack1 ->
                     (FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25854  ->
                           let uu____25855 =
                             FStar_Syntax_Print.term_to_string t1  in
                           FStar_Util.print1
                             "Rebuilding with match, scrutinee is %s ...\n"
                             uu____25855);
                      (let scrutinee_env = env  in
                       let env1 = env'  in
                       let scrutinee = t1  in
                       let norm_and_rebuild_match uu____25866 =
                         FStar_TypeChecker_Cfg.log cfg1
                           (fun uu____25871  ->
                              let uu____25872 =
                                FStar_Syntax_Print.term_to_string scrutinee
                                 in
                              let uu____25874 =
                                let uu____25876 =
                                  FStar_All.pipe_right branches
                                    (FStar_List.map
                                       (fun uu____25906  ->
                                          match uu____25906 with
                                          | (p,uu____25917,uu____25918) ->
                                              FStar_Syntax_Print.pat_to_string
                                                p))
                                   in
                                FStar_All.pipe_right uu____25876
                                  (FStar_String.concat "\n\t")
                                 in
                              FStar_Util.print2
                                "match is irreducible: scrutinee=%s\nbranches=%s\n"
                                uu____25872 uu____25874);
                         (let whnf =
                            (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                              ||
                              (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.hnf
                             in
                          let cfg_exclude_zeta =
                            let new_delta =
                              FStar_All.pipe_right
                                cfg1.FStar_TypeChecker_Cfg.delta_level
                                (FStar_List.filter
                                   (fun uu___16_25940  ->
                                      match uu___16_25940 with
                                      | FStar_TypeChecker_Env.InliningDelta 
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                           -> true
                                      | uu____25944 -> false))
                               in
                            let steps =
                              let uu___3112_25947 =
                                cfg1.FStar_TypeChecker_Cfg.steps  in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3112_25947.FStar_TypeChecker_Cfg.for_extraction)
                              }  in
                            let uu___3115_25954 = cfg1  in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3115_25954.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3115_25954.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3115_25954.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3115_25954.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3115_25954.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3115_25954.FStar_TypeChecker_Cfg.reifying)
                            }  in
                          let norm_or_whnf env2 t2 =
                            if whnf
                            then closure_as_term cfg_exclude_zeta env2 t2
                            else norm cfg_exclude_zeta env2 [] t2  in
                          let rec norm_pat env2 p =
                            match p.FStar_Syntax_Syntax.v with
                            | FStar_Syntax_Syntax.Pat_constant uu____26029 ->
                                (p, env2)
                            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                                let uu____26060 =
                                  FStar_All.pipe_right pats
                                    (FStar_List.fold_left
                                       (fun uu____26149  ->
                                          fun uu____26150  ->
                                            match (uu____26149, uu____26150)
                                            with
                                            | ((pats1,env3),(p1,b)) ->
                                                let uu____26300 =
                                                  norm_pat env3 p1  in
                                                (match uu____26300 with
                                                 | (p2,env4) ->
                                                     (((p2, b) :: pats1),
                                                       env4))) ([], env2))
                                   in
                                (match uu____26060 with
                                 | (pats1,env3) ->
                                     ((let uu___3143_26470 = p  in
                                       {
                                         FStar_Syntax_Syntax.v =
                                           (FStar_Syntax_Syntax.Pat_cons
                                              (fv, (FStar_List.rev pats1)));
                                         FStar_Syntax_Syntax.p =
                                           (uu___3143_26470.FStar_Syntax_Syntax.p)
                                       }), env3))
                            | FStar_Syntax_Syntax.Pat_var x ->
                                let x1 =
                                  let uu___3147_26491 = x  in
                                  let uu____26492 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3147_26491.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3147_26491.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26492
                                  }  in
                                ((let uu___3150_26506 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_var x1);
                                    FStar_Syntax_Syntax.p =
                                      (uu___3150_26506.FStar_Syntax_Syntax.p)
                                  }), (dummy :: env2))
                            | FStar_Syntax_Syntax.Pat_wild x ->
                                let x1 =
                                  let uu___3154_26517 = x  in
                                  let uu____26518 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3154_26517.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3154_26517.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26518
                                  }  in
                                ((let uu___3157_26532 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_wild x1);
                                    FStar_Syntax_Syntax.p =
                                      (uu___3157_26532.FStar_Syntax_Syntax.p)
                                  }), (dummy :: env2))
                            | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                                let x1 =
                                  let uu___3163_26548 = x  in
                                  let uu____26549 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3163_26548.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3163_26548.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26549
                                  }  in
                                let t3 = norm_or_whnf env2 t2  in
                                ((let uu___3167_26564 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_dot_term
                                         (x1, t3));
                                    FStar_Syntax_Syntax.p =
                                      (uu___3167_26564.FStar_Syntax_Syntax.p)
                                  }), env2)
                             in
                          let branches1 =
                            match env1 with
                            | [] when whnf -> branches
                            | uu____26608 ->
                                FStar_All.pipe_right branches
                                  (FStar_List.map
                                     (fun branch1  ->
                                        let uu____26638 =
                                          FStar_Syntax_Subst.open_branch
                                            branch1
                                           in
                                        match uu____26638 with
                                        | (p,wopt,e) ->
                                            let uu____26658 = norm_pat env1 p
                                               in
                                            (match uu____26658 with
                                             | (p1,env2) ->
                                                 let wopt1 =
                                                   match wopt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       FStar_Pervasives_Native.None
                                                   | FStar_Pervasives_Native.Some
                                                       w ->
                                                       let uu____26713 =
                                                         norm_or_whnf env2 w
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____26713
                                                    in
                                                 let e1 = norm_or_whnf env2 e
                                                    in
                                                 FStar_Syntax_Util.branch
                                                   (p1, wopt1, e1))))
                             in
                          let scrutinee1 =
                            let uu____26730 =
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
                            if uu____26730
                            then
                              norm
                                (let uu___3186_26737 = cfg1  in
                                 {
                                   FStar_TypeChecker_Cfg.steps =
                                     (let uu___3188_26740 =
                                        cfg1.FStar_TypeChecker_Cfg.steps  in
                                      {
                                        FStar_TypeChecker_Cfg.beta =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.beta);
                                        FStar_TypeChecker_Cfg.iota =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.iota);
                                        FStar_TypeChecker_Cfg.zeta =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.zeta);
                                        FStar_TypeChecker_Cfg.weak =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.weak);
                                        FStar_TypeChecker_Cfg.hnf =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.hnf);
                                        FStar_TypeChecker_Cfg.primops =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.primops);
                                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                          =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                        FStar_TypeChecker_Cfg.unfold_until =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.unfold_until);
                                        FStar_TypeChecker_Cfg.unfold_only =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.unfold_only);
                                        FStar_TypeChecker_Cfg.unfold_fully =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.unfold_fully);
                                        FStar_TypeChecker_Cfg.unfold_attr =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.unfold_attr);
                                        FStar_TypeChecker_Cfg.unfold_tac =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.unfold_tac);
                                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                          =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                        FStar_TypeChecker_Cfg.simplify =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.simplify);
                                        FStar_TypeChecker_Cfg.erase_universes
                                          =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.erase_universes);
                                        FStar_TypeChecker_Cfg.allow_unbound_universes
                                          =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                        FStar_TypeChecker_Cfg.reify_ =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.reify_);
                                        FStar_TypeChecker_Cfg.compress_uvars
                                          =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.compress_uvars);
                                        FStar_TypeChecker_Cfg.no_full_norm =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.no_full_norm);
                                        FStar_TypeChecker_Cfg.check_no_uvars
                                          =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.check_no_uvars);
                                        FStar_TypeChecker_Cfg.unmeta =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.unmeta);
                                        FStar_TypeChecker_Cfg.unascribe =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.unascribe);
                                        FStar_TypeChecker_Cfg.in_full_norm_request
                                          =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.in_full_norm_request);
                                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                          = false;
                                        FStar_TypeChecker_Cfg.nbe_step =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.nbe_step);
                                        FStar_TypeChecker_Cfg.for_extraction
                                          =
                                          (uu___3188_26740.FStar_TypeChecker_Cfg.for_extraction)
                                      });
                                   FStar_TypeChecker_Cfg.tcenv =
                                     (uu___3186_26737.FStar_TypeChecker_Cfg.tcenv);
                                   FStar_TypeChecker_Cfg.debug =
                                     (uu___3186_26737.FStar_TypeChecker_Cfg.debug);
                                   FStar_TypeChecker_Cfg.delta_level =
                                     (uu___3186_26737.FStar_TypeChecker_Cfg.delta_level);
                                   FStar_TypeChecker_Cfg.primitive_steps =
                                     (uu___3186_26737.FStar_TypeChecker_Cfg.primitive_steps);
                                   FStar_TypeChecker_Cfg.strong =
                                     (uu___3186_26737.FStar_TypeChecker_Cfg.strong);
                                   FStar_TypeChecker_Cfg.memoize_lazy =
                                     (uu___3186_26737.FStar_TypeChecker_Cfg.memoize_lazy);
                                   FStar_TypeChecker_Cfg.normalize_pure_lets
                                     =
                                     (uu___3186_26737.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                   FStar_TypeChecker_Cfg.reifying =
                                     (uu___3186_26737.FStar_TypeChecker_Cfg.reifying)
                                 }) scrutinee_env [] scrutinee
                            else scrutinee  in
                          let uu____26744 =
                            mk
                              (FStar_Syntax_Syntax.Tm_match
                                 (scrutinee1, branches1)) r
                             in
                          rebuild cfg1 env1 stack1 uu____26744)
                          in
                       let rec is_cons head1 =
                         let uu____26770 =
                           let uu____26771 =
                             FStar_Syntax_Subst.compress head1  in
                           uu____26771.FStar_Syntax_Syntax.n  in
                         match uu____26770 with
                         | FStar_Syntax_Syntax.Tm_uinst (h,uu____26776) ->
                             is_cons h
                         | FStar_Syntax_Syntax.Tm_constant uu____26781 ->
                             true
                         | FStar_Syntax_Syntax.Tm_fvar
                             { FStar_Syntax_Syntax.fv_name = uu____26783;
                               FStar_Syntax_Syntax.fv_delta = uu____26784;
                               FStar_Syntax_Syntax.fv_qual =
                                 FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Data_ctor );_}
                             -> true
                         | FStar_Syntax_Syntax.Tm_fvar
                             { FStar_Syntax_Syntax.fv_name = uu____26786;
                               FStar_Syntax_Syntax.fv_delta = uu____26787;
                               FStar_Syntax_Syntax.fv_qual =
                                 FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Record_ctor
                                 uu____26788);_}
                             -> true
                         | uu____26796 -> false  in
                       let guard_when_clause wopt b rest =
                         match wopt with
                         | FStar_Pervasives_Native.None  -> b
                         | FStar_Pervasives_Native.Some w ->
                             let then_branch = b  in
                             let else_branch =
                               mk
                                 (FStar_Syntax_Syntax.Tm_match
                                    (scrutinee, rest)) r
                                in
                             FStar_Syntax_Util.if_then_else w then_branch
                               else_branch
                          in
                       let rec matches_pat scrutinee_orig p =
                         let scrutinee1 =
                           FStar_Syntax_Util.unmeta scrutinee_orig  in
                         let scrutinee2 = FStar_Syntax_Util.unlazy scrutinee1
                            in
                         let uu____26965 =
                           FStar_Syntax_Util.head_and_args scrutinee2  in
                         match uu____26965 with
                         | (head1,args) ->
                             (match p.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_var bv ->
                                  FStar_Util.Inl [(bv, scrutinee_orig)]
                              | FStar_Syntax_Syntax.Pat_wild bv ->
                                  FStar_Util.Inl [(bv, scrutinee_orig)]
                              | FStar_Syntax_Syntax.Pat_dot_term uu____27062
                                  -> FStar_Util.Inl []
                              | FStar_Syntax_Syntax.Pat_constant s ->
                                  (match scrutinee2.FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_constant s' when
                                       FStar_Const.eq_const s s' ->
                                       FStar_Util.Inl []
                                   | uu____27104 ->
                                       let uu____27105 =
                                         let uu____27107 = is_cons head1  in
                                         Prims.op_Negation uu____27107  in
                                       FStar_Util.Inr uu____27105)
                              | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                                  let uu____27136 =
                                    let uu____27137 =
                                      FStar_Syntax_Util.un_uinst head1  in
                                    uu____27137.FStar_Syntax_Syntax.n  in
                                  (match uu____27136 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv' when
                                       FStar_Syntax_Syntax.fv_eq fv fv' ->
                                       matches_args [] args arg_pats
                                   | uu____27156 ->
                                       let uu____27157 =
                                         let uu____27159 = is_cons head1  in
                                         Prims.op_Negation uu____27159  in
                                       FStar_Util.Inr uu____27157))
                       
                       and matches_args out a p =
                         match (a, p) with
                         | ([],[]) -> FStar_Util.Inl out
                         | ((t2,uu____27250)::rest_a,(p1,uu____27253)::rest_p)
                             ->
                             let uu____27312 = matches_pat t2 p1  in
                             (match uu____27312 with
                              | FStar_Util.Inl s ->
                                  matches_args (FStar_List.append out s)
                                    rest_a rest_p
                              | m -> m)
                         | uu____27365 -> FStar_Util.Inr false
                        in
                       let rec matches scrutinee1 p =
                         match p with
                         | [] -> norm_and_rebuild_match ()
                         | (p1,wopt,b)::rest ->
                             let uu____27488 = matches_pat scrutinee1 p1  in
                             (match uu____27488 with
                              | FStar_Util.Inr (false ) ->
                                  matches scrutinee1 rest
                              | FStar_Util.Inr (true ) ->
                                  norm_and_rebuild_match ()
                              | FStar_Util.Inl s ->
                                  (FStar_TypeChecker_Cfg.log cfg1
                                     (fun uu____27534  ->
                                        let uu____27535 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        let uu____27537 =
                                          let uu____27539 =
                                            FStar_List.map
                                              (fun uu____27551  ->
                                                 match uu____27551 with
                                                 | (uu____27557,t2) ->
                                                     FStar_Syntax_Print.term_to_string
                                                       t2) s
                                             in
                                          FStar_All.pipe_right uu____27539
                                            (FStar_String.concat "; ")
                                           in
                                        FStar_Util.print2
                                          "Matches pattern %s with subst = %s\n"
                                          uu____27535 uu____27537);
                                   (let env0 = env1  in
                                    let env2 =
                                      FStar_List.fold_left
                                        (fun env2  ->
                                           fun uu____27593  ->
                                             match uu____27593 with
                                             | (bv,t2) ->
                                                 let uu____27616 =
                                                   let uu____27623 =
                                                     let uu____27626 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         bv
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____27626
                                                      in
                                                   let uu____27627 =
                                                     let uu____27628 =
                                                       let uu____27660 =
                                                         FStar_Util.mk_ref
                                                           (FStar_Pervasives_Native.Some
                                                              ([], t2))
                                                          in
                                                       ([], t2, uu____27660,
                                                         false)
                                                        in
                                                     Clos uu____27628  in
                                                   (uu____27623, uu____27627)
                                                    in
                                                 uu____27616 :: env2) env1 s
                                       in
                                    let uu____27753 =
                                      guard_when_clause wopt b rest  in
                                    norm cfg1 env2 stack1 uu____27753)))
                          in
                       if
                         (cfg1.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.iota
                       then matches scrutinee branches
                       else norm_and_rebuild_match ())))))

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
            (fun uu____27786  ->
               let uu____27787 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____27787);
          (let uu____27790 = is_nbe_request s  in
           if uu____27790
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27796  ->
                   let uu____27797 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27797);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27803  ->
                   let uu____27804 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27804);
              (let uu____27807 =
                 FStar_Util.record_time (fun uu____27814  -> nbe_eval c s t)
                  in
               match uu____27807 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27823  ->
                         let uu____27824 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27826 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27824 uu____27826);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27834  ->
                   let uu____27835 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27835);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27841  ->
                   let uu____27842 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27842);
              (let uu____27845 =
                 FStar_Util.record_time (fun uu____27852  -> norm c [] [] t)
                  in
               match uu____27845 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27867  ->
                         let uu____27868 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27870 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27868 uu____27870);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27889 =
          let uu____27893 =
            let uu____27895 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____27895  in
          FStar_Pervasives_Native.Some uu____27893  in
        FStar_Profiling.profile
          (fun uu____27898  -> normalize_with_primitive_steps [] s e t)
          uu____27889 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____27920  ->
             let uu____27921 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27921);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27927  ->
             let uu____27928 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27928);
        (let uu____27931 =
           FStar_Util.record_time (fun uu____27938  -> norm_comp cfg [] c)
            in
         match uu____27931 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27953  ->
                   let uu____27954 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____27956 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27954
                     uu____27956);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27970 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____27970 [] u
  
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
      let uu____27992 = normalize steps env t  in
      FStar_TypeChecker_Env.non_informative env uu____27992
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____28004 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env t ->
          let uu___3356_28023 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3356_28023.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3356_28023.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____28030 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____28030
          then
            let ct1 =
              let uu____28034 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____28034 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____28041 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____28041
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3366_28048 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3366_28048.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3366_28048.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3366_28048.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c
                     in
                  let uu___3370_28050 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3370_28050.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3370_28050.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3370_28050.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3370_28050.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3373_28051 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3373_28051.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3373_28051.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____28054 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      let uu____28066 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____28066
      then
        let uu____28069 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____28069 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3381_28073 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3381_28073.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3381_28073.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3381_28073.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3388_28092  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3387_28095 ->
            ((let uu____28097 =
                let uu____28103 =
                  let uu____28105 = FStar_Util.message_of_exn uu___3387_28095
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____28105
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____28103)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____28097);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3398_28124  ->
             match () with
             | () ->
                 let uu____28125 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____28125 [] c) ()
        with
        | uu___3397_28134 ->
            ((let uu____28136 =
                let uu____28142 =
                  let uu____28144 = FStar_Util.message_of_exn uu___3397_28134
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____28144
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____28142)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____28136);
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
                   let uu____28193 =
                     let uu____28194 =
                       let uu____28201 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____28201)  in
                     FStar_Syntax_Syntax.Tm_refine uu____28194  in
                   mk uu____28193 t01.FStar_Syntax_Syntax.pos
               | uu____28206 -> t2)
          | uu____28207 -> t2  in
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
        let uu____28301 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____28301 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____28338 ->
                 let uu____28347 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____28347 with
                  | (actuals,uu____28357,uu____28358) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____28378 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____28378 with
                         | (binders,args) ->
                             let uu____28389 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____28389
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
      | uu____28404 ->
          let uu____28405 = FStar_Syntax_Util.head_and_args t  in
          (match uu____28405 with
           | (head1,args) ->
               let uu____28448 =
                 let uu____28449 = FStar_Syntax_Subst.compress head1  in
                 uu____28449.FStar_Syntax_Syntax.n  in
               (match uu____28448 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____28470 =
                      let uu____28485 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____28485  in
                    (match uu____28470 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____28525 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3468_28533 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3468_28533.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3468_28533.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3468_28533.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3468_28533.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3468_28533.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3468_28533.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3468_28533.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3468_28533.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3468_28533.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3468_28533.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3468_28533.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3468_28533.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3468_28533.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3468_28533.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3468_28533.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3468_28533.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3468_28533.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3468_28533.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3468_28533.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3468_28533.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3468_28533.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3468_28533.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3468_28533.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3468_28533.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3468_28533.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3468_28533.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3468_28533.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3468_28533.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3468_28533.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3468_28533.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3468_28533.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3468_28533.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3468_28533.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3468_28533.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3468_28533.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3468_28533.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3468_28533.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3468_28533.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3468_28533.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3468_28533.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3468_28533.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3468_28533.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3468_28533.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____28525 with
                            | (uu____28536,ty,uu____28538) ->
                                eta_expand_with_type env t ty))
                | uu____28539 ->
                    let uu____28540 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3475_28548 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3475_28548.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3475_28548.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3475_28548.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3475_28548.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3475_28548.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3475_28548.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3475_28548.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3475_28548.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3475_28548.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3475_28548.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3475_28548.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3475_28548.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3475_28548.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3475_28548.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3475_28548.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3475_28548.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3475_28548.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3475_28548.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3475_28548.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3475_28548.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3475_28548.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3475_28548.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3475_28548.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3475_28548.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3475_28548.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3475_28548.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3475_28548.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3475_28548.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3475_28548.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3475_28548.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3475_28548.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3475_28548.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3475_28548.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3475_28548.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3475_28548.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3475_28548.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3475_28548.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3475_28548.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3475_28548.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3475_28548.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3475_28548.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3475_28548.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3475_28548.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____28540 with
                     | (uu____28551,ty,uu____28553) ->
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
      let uu___3487_28635 = x  in
      let uu____28636 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3487_28635.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3487_28635.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28636
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28639 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28663 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28664 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28665 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28666 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28673 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28674 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28675 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3513_28709 = rc  in
          let uu____28710 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28719 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3513_28709.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28710;
            FStar_Syntax_Syntax.residual_flags = uu____28719
          }  in
        let uu____28722 =
          let uu____28723 =
            let uu____28742 = elim_delayed_subst_binders bs  in
            let uu____28751 = elim_delayed_subst_term t2  in
            let uu____28754 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28742, uu____28751, uu____28754)  in
          FStar_Syntax_Syntax.Tm_abs uu____28723  in
        mk1 uu____28722
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28791 =
          let uu____28792 =
            let uu____28807 = elim_delayed_subst_binders bs  in
            let uu____28816 = elim_delayed_subst_comp c  in
            (uu____28807, uu____28816)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28792  in
        mk1 uu____28791
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28835 =
          let uu____28836 =
            let uu____28843 = elim_bv bv  in
            let uu____28844 = elim_delayed_subst_term phi  in
            (uu____28843, uu____28844)  in
          FStar_Syntax_Syntax.Tm_refine uu____28836  in
        mk1 uu____28835
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28875 =
          let uu____28876 =
            let uu____28893 = elim_delayed_subst_term t2  in
            let uu____28896 = elim_delayed_subst_args args  in
            (uu____28893, uu____28896)  in
          FStar_Syntax_Syntax.Tm_app uu____28876  in
        mk1 uu____28875
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3535_28968 = p  in
              let uu____28969 =
                let uu____28970 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28970  in
              {
                FStar_Syntax_Syntax.v = uu____28969;
                FStar_Syntax_Syntax.p =
                  (uu___3535_28968.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3539_28972 = p  in
              let uu____28973 =
                let uu____28974 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28974  in
              {
                FStar_Syntax_Syntax.v = uu____28973;
                FStar_Syntax_Syntax.p =
                  (uu___3539_28972.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3545_28981 = p  in
              let uu____28982 =
                let uu____28983 =
                  let uu____28990 = elim_bv x  in
                  let uu____28991 = elim_delayed_subst_term t0  in
                  (uu____28990, uu____28991)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28983  in
              {
                FStar_Syntax_Syntax.v = uu____28982;
                FStar_Syntax_Syntax.p =
                  (uu___3545_28981.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3551_29016 = p  in
              let uu____29017 =
                let uu____29018 =
                  let uu____29032 =
                    FStar_List.map
                      (fun uu____29058  ->
                         match uu____29058 with
                         | (x,b) ->
                             let uu____29075 = elim_pat x  in
                             (uu____29075, b)) pats
                     in
                  (fv, uu____29032)  in
                FStar_Syntax_Syntax.Pat_cons uu____29018  in
              {
                FStar_Syntax_Syntax.v = uu____29017;
                FStar_Syntax_Syntax.p =
                  (uu___3551_29016.FStar_Syntax_Syntax.p)
              }
          | uu____29090 -> p  in
        let elim_branch uu____29114 =
          match uu____29114 with
          | (pat,wopt,t3) ->
              let uu____29140 = elim_pat pat  in
              let uu____29143 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____29146 = elim_delayed_subst_term t3  in
              (uu____29140, uu____29143, uu____29146)
           in
        let uu____29151 =
          let uu____29152 =
            let uu____29175 = elim_delayed_subst_term t2  in
            let uu____29178 = FStar_List.map elim_branch branches  in
            (uu____29175, uu____29178)  in
          FStar_Syntax_Syntax.Tm_match uu____29152  in
        mk1 uu____29151
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____29309 =
          match uu____29309 with
          | (tc,topt) ->
              let uu____29344 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____29354 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____29354
                | FStar_Util.Inr c ->
                    let uu____29356 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____29356
                 in
              let uu____29357 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____29344, uu____29357)
           in
        let uu____29366 =
          let uu____29367 =
            let uu____29394 = elim_delayed_subst_term t2  in
            let uu____29397 = elim_ascription a  in
            (uu____29394, uu____29397, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____29367  in
        mk1 uu____29366
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3581_29460 = lb  in
          let uu____29461 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____29464 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3581_29460.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3581_29460.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____29461;
            FStar_Syntax_Syntax.lbeff =
              (uu___3581_29460.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____29464;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3581_29460.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3581_29460.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____29467 =
          let uu____29468 =
            let uu____29482 =
              let uu____29490 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____29490)  in
            let uu____29502 = elim_delayed_subst_term t2  in
            (uu____29482, uu____29502)  in
          FStar_Syntax_Syntax.Tm_let uu____29468  in
        mk1 uu____29467
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____29547 =
          let uu____29548 =
            let uu____29555 = elim_delayed_subst_term tm  in
            (uu____29555, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____29548  in
        mk1 uu____29547
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29566 =
          let uu____29567 =
            let uu____29574 = elim_delayed_subst_term t2  in
            let uu____29577 = elim_delayed_subst_meta md  in
            (uu____29574, uu____29577)  in
          FStar_Syntax_Syntax.Tm_meta uu____29567  in
        mk1 uu____29566

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29586  ->
         match uu___17_29586 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29590 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29590
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
        let uu____29613 =
          let uu____29614 =
            let uu____29623 = elim_delayed_subst_term t  in
            (uu____29623, uopt)  in
          FStar_Syntax_Syntax.Total uu____29614  in
        mk1 uu____29613
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29640 =
          let uu____29641 =
            let uu____29650 = elim_delayed_subst_term t  in
            (uu____29650, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29641  in
        mk1 uu____29640
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3614_29659 = ct  in
          let uu____29660 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29663 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29674 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3614_29659.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3614_29659.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29660;
            FStar_Syntax_Syntax.effect_args = uu____29663;
            FStar_Syntax_Syntax.flags = uu____29674
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29677  ->
    match uu___18_29677 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____29712 =
          let uu____29733 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____29742 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29733, uu____29742)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29712
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____29797 =
          let uu____29804 = elim_delayed_subst_term t  in (m, uu____29804)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____29797
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____29816 =
          let uu____29825 = elim_delayed_subst_term t  in
          (m1, m2, uu____29825)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29816
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
      (fun uu____29858  ->
         match uu____29858 with
         | (t,q) ->
             let uu____29877 = elim_delayed_subst_term t  in (uu____29877, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29905  ->
         match uu____29905 with
         | (x,q) ->
             let uu____29924 =
               let uu___3640_29925 = x  in
               let uu____29926 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3640_29925.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3640_29925.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29926
               }  in
             (uu____29924, q)) bs

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
            | (uu____30034,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____30066,FStar_Util.Inl t) ->
                let uu____30088 =
                  let uu____30095 =
                    let uu____30096 =
                      let uu____30111 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____30111)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____30096  in
                  FStar_Syntax_Syntax.mk uu____30095  in
                uu____30088 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____30124 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____30124 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____30156 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____30229 ->
                    let uu____30230 =
                      let uu____30239 =
                        let uu____30240 = FStar_Syntax_Subst.compress t4  in
                        uu____30240.FStar_Syntax_Syntax.n  in
                      (uu____30239, tc)  in
                    (match uu____30230 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____30269) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____30316) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____30361,FStar_Util.Inl uu____30362) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____30393 -> failwith "Impossible")
                 in
              (match uu____30156 with
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
          let uu____30532 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____30532 with
          | (univ_names1,binders1,tc) ->
              let uu____30606 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30606)
  
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
          let uu____30660 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____30660 with
          | (univ_names1,binders1,tc) ->
              let uu____30734 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30734)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____30776 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____30776 with
           | (univ_names1,binders1,typ1) ->
               let uu___3723_30816 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3723_30816.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3723_30816.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3723_30816.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3723_30816.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3723_30816.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3729_30831 = s  in
          let uu____30832 =
            let uu____30833 =
              let uu____30842 = FStar_List.map (elim_uvars env) sigs  in
              (uu____30842, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____30833  in
          {
            FStar_Syntax_Syntax.sigel = uu____30832;
            FStar_Syntax_Syntax.sigrng =
              (uu___3729_30831.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3729_30831.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3729_30831.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3729_30831.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3729_30831.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____30861 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30861 with
           | (univ_names1,uu____30885,typ1) ->
               let uu___3743_30907 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3743_30907.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3743_30907.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3743_30907.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3743_30907.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3743_30907.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____30914 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30914 with
           | (univ_names1,uu____30938,typ1) ->
               let uu___3754_30960 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3754_30960.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3754_30960.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3754_30960.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3754_30960.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3754_30960.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30990 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30990 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____31015 =
                            let uu____31016 =
                              let uu____31017 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____31017  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____31016
                             in
                          elim_delayed_subst_term uu____31015  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3770_31020 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3770_31020.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3770_31020.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3770_31020.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3770_31020.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3773_31021 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3773_31021.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3773_31021.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3773_31021.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3773_31021.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3773_31021.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3777_31028 = s  in
          let uu____31029 =
            let uu____31030 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____31030  in
          {
            FStar_Syntax_Syntax.sigel = uu____31029;
            FStar_Syntax_Syntax.sigrng =
              (uu___3777_31028.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3777_31028.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3777_31028.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3777_31028.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3777_31028.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____31034 = elim_uvars_aux_t env us [] t  in
          (match uu____31034 with
           | (us1,uu____31058,t1) ->
               let uu___3788_31080 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3788_31080.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3788_31080.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3788_31080.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3788_31080.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3788_31080.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____31082 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____31082 with
           | (univs1,binders,uu____31101) ->
               let uu____31122 =
                 let uu____31127 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____31127 with
                 | (univs_opening,univs2) ->
                     let uu____31150 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____31150)
                  in
               (match uu____31122 with
                | (univs_opening,univs_closing) ->
                    let uu____31153 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____31159 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____31160 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____31159, uu____31160)  in
                    (match uu____31153 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____31186 =
                           match uu____31186 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____31204 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____31204 with
                                | (us1,t1) ->
                                    let uu____31215 =
                                      let uu____31224 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____31229 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____31224, uu____31229)  in
                                    (match uu____31215 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____31252 =
                                           let uu____31261 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____31266 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____31261, uu____31266)  in
                                         (match uu____31252 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____31290 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____31290
                                                 in
                                              let uu____31291 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____31291 with
                                               | (uu____31318,uu____31319,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____31342 =
                                                       let uu____31343 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____31343
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____31342
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____31352 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____31352 with
                           | (uu____31371,uu____31372,t1) -> t1  in
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
                             | uu____31448 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____31475 =
                               let uu____31476 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____31476.FStar_Syntax_Syntax.n  in
                             match uu____31475 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____31535 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31569 =
                               let uu____31570 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31570.FStar_Syntax_Syntax.n  in
                             match uu____31569 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31593) ->
                                 let uu____31618 = destruct_action_body body
                                    in
                                 (match uu____31618 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31667 ->
                                 let uu____31668 = destruct_action_body t  in
                                 (match uu____31668 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31723 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31723 with
                           | (action_univs,t) ->
                               let uu____31732 = destruct_action_typ_templ t
                                  in
                               (match uu____31732 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3872_31779 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3872_31779.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3872_31779.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3875_31781 = ed  in
                           let uu____31782 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____31783 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____31784 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3875_31781.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3875_31781.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31782;
                             FStar_Syntax_Syntax.combinators = uu____31783;
                             FStar_Syntax_Syntax.actions = uu____31784;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3875_31781.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3878_31787 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3878_31787.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3878_31787.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3878_31787.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3878_31787.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3878_31787.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31808 =
            match uu___19_31808 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____31839 = elim_uvars_aux_t env us [] t  in
                (match uu____31839 with
                 | (us1,uu____31871,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3893_31902 = sub_eff  in
            let uu____31903 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____31906 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3893_31902.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3893_31902.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31903;
              FStar_Syntax_Syntax.lift = uu____31906
            }  in
          let uu___3896_31909 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3896_31909.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3896_31909.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3896_31909.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3896_31909.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3896_31909.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____31919 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____31919 with
           | (univ_names1,binders1,comp1) ->
               let uu___3909_31959 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3909_31959.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3909_31959.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3909_31959.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3909_31959.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3909_31959.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31962 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31963 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n1,p,(us_t,t),(us_ty,ty))
          ->
          let uu____31993 = elim_uvars_aux_t env us_t [] t  in
          (match uu____31993 with
           | (us_t1,uu____32017,t1) ->
               let uu____32039 = elim_uvars_aux_t env us_ty [] ty  in
               (match uu____32039 with
                | (us_ty1,uu____32063,ty1) ->
                    let uu___3934_32085 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n1, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3934_32085.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3934_32085.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3934_32085.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3934_32085.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3934_32085.FStar_Syntax_Syntax.sigopts)
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
        let uu____32136 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____32136 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____32158 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____32158 with
             | (uu____32165,head_def) ->
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
      let uu____32171 = FStar_Syntax_Util.head_and_args t  in
      match uu____32171 with
      | (head1,args) ->
          let uu____32216 =
            let uu____32217 = FStar_Syntax_Subst.compress head1  in
            uu____32217.FStar_Syntax_Syntax.n  in
          (match uu____32216 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____32224;
                  FStar_Syntax_Syntax.vars = uu____32225;_},us)
               -> aux fv us args
           | uu____32231 -> FStar_Pervasives_Native.None)
  