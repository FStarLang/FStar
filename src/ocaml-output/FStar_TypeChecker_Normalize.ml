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
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            FStar_Syntax_Syntax.fv_eq_lid fv lid
        | uu____9479 -> false  in
      let us_of t1 =
        let uu____9487 =
          let uu____9488 = FStar_Syntax_Subst.compress t1  in
          uu____9488.FStar_Syntax_Syntax.n  in
        match uu____9487 with
        | FStar_Syntax_Syntax.Tm_uinst (uu____9491,us) -> us
        | FStar_Syntax_Syntax.Tm_fvar uu____9497 -> []
        | uu____9498 ->
            failwith "Impossible! us_of called with a non Tm_uinst term"
         in
      let mk_app1 lid us args r =
        let uu____9521 =
          let uu____9522 =
            let uu____9523 =
              FStar_Syntax_Syntax.lid_as_fv lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                FStar_Pervasives_Native.None
               in
            FStar_All.pipe_right uu____9523 FStar_Syntax_Syntax.fv_to_tm  in
          FStar_All.pipe_right uu____9522
            (fun t1  -> FStar_Syntax_Syntax.mk_Tm_uinst t1 us)
           in
        FStar_All.pipe_right uu____9521
          (fun f  ->
             FStar_Syntax_Syntax.mk_Tm_app f args
               FStar_Pervasives_Native.None r)
         in
      let reduce_as_requires args r =
        if (FStar_List.length args) <> (Prims.of_int (2))
        then FStar_Pervasives_Native.None
        else
          (let uu____9559 = args  in
           match uu____9559 with
           | uu____9562::(wp,uu____9564)::[] ->
               let uu____9605 =
                 let uu____9606 = FStar_Syntax_Subst.compress wp  in
                 uu____9606.FStar_Syntax_Syntax.n  in
               (match uu____9605 with
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.as_wp ->
                    let uu____9637 = args1  in
                    (match uu____9637 with
                     | uu____9650::(req,uu____9652)::uu____9653::[] ->
                         FStar_Pervasives_Native.Some req)
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_return_lid ->
                    let uu____9736 =
                      let uu____9737 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_return uu____9737
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9740  -> FStar_Pervasives_Native.Some _9740)
                      uu____9736
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_bind_lid ->
                    let uu____9767 =
                      let uu____9768 = us_of head1  in
                      let uu____9769 =
                        FStar_All.pipe_right args1 FStar_List.tl  in
                      mk_app1 FStar_Parser_Const.as_req_bind uu____9768
                        uu____9769 r
                       in
                    FStar_All.pipe_left
                      (fun _9790  -> FStar_Pervasives_Native.Some _9790)
                      uu____9767
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_assume_wp_lid ->
                    let uu____9817 =
                      let uu____9818 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_assume uu____9818
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9821  -> FStar_Pervasives_Native.Some _9821)
                      uu____9817
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_assert_wp_lid ->
                    let uu____9848 =
                      let uu____9849 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_assert uu____9849
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9852  -> FStar_Pervasives_Native.Some _9852)
                      uu____9848
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_if_then_else_lid ->
                    let uu____9879 =
                      let uu____9880 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_if_then_else
                        uu____9880 args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9883  -> FStar_Pervasives_Native.Some _9883)
                      uu____9879
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_ite_lid ->
                    let uu____9910 =
                      let uu____9911 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_ite uu____9911 args1
                        r
                       in
                    FStar_All.pipe_left
                      (fun _9914  -> FStar_Pervasives_Native.Some _9914)
                      uu____9910
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_close_lid ->
                    let uu____9941 =
                      let uu____9942 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_close uu____9942
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9945  -> FStar_Pervasives_Native.Some _9945)
                      uu____9941
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_null_lid ->
                    let uu____9972 =
                      let uu____9973 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_null uu____9973 args1
                        r
                       in
                    FStar_All.pipe_left
                      (fun _9976  -> FStar_Pervasives_Native.Some _9976)
                      uu____9972
                | uu____9977 -> FStar_Pervasives_Native.None))
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
               let uu____10028 = args  in
               match uu____10028 with
               | uu____10029::(wp,uu____10031)::[] -> wp
             else
               (let uu____10074 = args  in
                match uu____10074 with
                | uu____10075::(wp,uu____10077)::uu____10078::[] -> wp)
              in
           let uu____10135 =
             let uu____10136 = FStar_Syntax_Subst.compress wp  in
             uu____10136.FStar_Syntax_Syntax.n  in
           match uu____10135 with
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.as_wp ->
               let uu____10167 = args1  in
               (match uu____10167 with
                | uu____10180::uu____10181::(ens,uu____10183)::[] ->
                    FStar_Pervasives_Native.Some ens)
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_return_lid ->
               let uu____10266 =
                 let uu____10267 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_return uu____10267 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10270  -> FStar_Pervasives_Native.Some _10270)
                 uu____10266
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_bind_lid ->
               let uu____10297 =
                 let uu____10298 = us_of head1  in
                 let uu____10299 = FStar_All.pipe_right args1 FStar_List.tl
                    in
                 mk_app1 FStar_Parser_Const.as_ens_bind uu____10298
                   uu____10299 r
                  in
               FStar_All.pipe_left
                 (fun _10320  -> FStar_Pervasives_Native.Some _10320)
                 uu____10297
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_assume_wp_lid ->
               let uu____10347 =
                 let uu____10348 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_assume uu____10348 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10351  -> FStar_Pervasives_Native.Some _10351)
                 uu____10347
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_assert_wp_lid ->
               let uu____10378 =
                 let uu____10379 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_assert uu____10379 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10382  -> FStar_Pervasives_Native.Some _10382)
                 uu____10378
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_if_then_else_lid ->
               let uu____10409 =
                 let uu____10410 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_if_then_else uu____10410
                   args1 r
                  in
               FStar_All.pipe_left
                 (fun _10413  -> FStar_Pervasives_Native.Some _10413)
                 uu____10409
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_ite_lid ->
               let uu____10440 =
                 let uu____10441 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_ite uu____10441 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10444  -> FStar_Pervasives_Native.Some _10444)
                 uu____10440
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_close_lid ->
               let uu____10471 =
                 let uu____10472 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_close uu____10472 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10475  -> FStar_Pervasives_Native.Some _10475)
                 uu____10471
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_null_lid ->
               let uu____10502 =
                 let uu____10503 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_null uu____10503 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10506  -> FStar_Pervasives_Native.Some _10506)
                 uu____10502
           | uu____10507 -> FStar_Pervasives_Native.None)
         in
      let uu____10508 =
        let uu____10509 = FStar_Syntax_Subst.compress t  in
        uu____10509.FStar_Syntax_Syntax.n  in
      match uu____10508 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) when
          is_fv head1 FStar_Parser_Const.as_requires_opaque ->
          reduce_as_requires args t.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) when
          is_fv head1 FStar_Parser_Const.as_ensures_opaque ->
          reduce_as_ensures args t.FStar_Syntax_Syntax.pos
      | uu____10566 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____10845 ->
                   let uu____10868 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____10868
               | uu____10871 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____10881  ->
               let uu____10882 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____10884 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____10886 = FStar_Syntax_Print.term_to_string t1  in
               let uu____10888 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____10896 =
                 let uu____10898 =
                   let uu____10901 = firstn (Prims.of_int (4)) stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10901
                    in
                 stack_to_string uu____10898  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____10882 uu____10884 uu____10886 uu____10888 uu____10896);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____10929  ->
               let uu____10930 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____10930);
          (let t_opt = is_wp_req_ens_commutation cfg t1  in
           let uu____10936 = FStar_All.pipe_right t_opt FStar_Util.is_some
              in
           if uu____10936
           then
             ((let uu____10943 =
                 FStar_All.pipe_left
                   (FStar_TypeChecker_Env.debug
                      cfg.FStar_TypeChecker_Cfg.tcenv)
                   (FStar_Options.Other "WPReqEns")
                  in
               if uu____10943
               then
                 let uu____10948 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10950 =
                   let uu____10952 =
                     FStar_All.pipe_right t_opt FStar_Util.must  in
                   FStar_All.pipe_right uu____10952
                     FStar_Syntax_Print.term_to_string
                    in
                 FStar_Util.print2
                   "Norm request identified as wp_req_ens commutation{, \n\nreduced %s \n\nto\n\n %s\n"
                   uu____10948 uu____10950
               else ());
              (let t2 = FStar_All.pipe_right t_opt FStar_Util.must  in
               let cfg_restricted =
                 FStar_TypeChecker_Cfg.config' []
                   [FStar_TypeChecker_Env.UnfoldAttr
                      [FStar_Parser_Const.wp_req_ens_attr]]
                   cfg.FStar_TypeChecker_Cfg.tcenv
                  in
               let t3 = norm cfg_restricted env [] t2  in
               (let uu____10965 =
                  FStar_All.pipe_left
                    (FStar_TypeChecker_Env.debug
                       cfg.FStar_TypeChecker_Cfg.tcenv)
                    (FStar_Options.Other "WPReqEns")
                   in
                if uu____10965
                then
                  let uu____10970 = FStar_Syntax_Print.term_to_string t3  in
                  FStar_Util.print1
                    "After norm in a restricted environment, t : %s\n}"
                    uu____10970
                else ());
               norm cfg env stack t3))
           else
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10980  ->
                        let uu____10981 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10981);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_constant uu____10984 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10988  ->
                        let uu____10989 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10989);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_name uu____10992 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10996  ->
                        let uu____10997 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10997);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_lazy uu____11000 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11004  ->
                        let uu____11005 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11005);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = uu____11008;
                    FStar_Syntax_Syntax.fv_delta = uu____11009;
                    FStar_Syntax_Syntax.fv_qual =
                      FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Data_ctor );_}
                  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11013  ->
                        let uu____11014 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11014);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = uu____11017;
                    FStar_Syntax_Syntax.fv_delta = uu____11018;
                    FStar_Syntax_Syntax.fv_qual =
                      FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor uu____11019);_}
                  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11029  ->
                        let uu____11030 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11030);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                  let qninfo =
                    FStar_TypeChecker_Env.lookup_qname
                      cfg.FStar_TypeChecker_Cfg.tcenv lid
                     in
                  let uu____11036 =
                    FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
                  (match uu____11036 with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Delta_constant_at_level _11039)
                       when _11039 = Prims.int_zero ->
                       (FStar_TypeChecker_Cfg.log_unfolding cfg
                          (fun uu____11043  ->
                             let uu____11044 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                               uu____11044);
                        rebuild cfg env stack t1)
                   | uu____11047 ->
                       let uu____11050 =
                         decide_unfolding cfg env stack
                           t1.FStar_Syntax_Syntax.pos fv qninfo
                          in
                       (match uu____11050 with
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
                  let uu____11089 = closure_as_term cfg env t2  in
                  rebuild cfg env stack uu____11089
              | FStar_Syntax_Syntax.Tm_app (hd1,args) when
                  (should_consider_norm_requests cfg) &&
                    (let uu____11117 = is_norm_request hd1 args  in
                     uu____11117 = Norm_request_requires_rejig)
                  ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     FStar_Util.print_string "Rejigging norm request ... \n"
                   else ();
                   (let uu____11123 = rejig_norm_request hd1 args  in
                    norm cfg env stack uu____11123))
              | FStar_Syntax_Syntax.Tm_app (hd1,args) when
                  (should_consider_norm_requests cfg) &&
                    (let uu____11151 = is_norm_request hd1 args  in
                     uu____11151 = Norm_request_ready)
                  ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     FStar_Util.print_string "Potential norm request ... \n"
                   else ();
                   (let cfg' =
                      let uu___1422_11158 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (let uu___1424_11161 =
                             cfg.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               false;
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1424_11161.FStar_TypeChecker_Cfg.for_extraction)
                           });
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1422_11158.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1422_11158.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          [FStar_TypeChecker_Env.Unfold
                             FStar_Syntax_Syntax.delta_constant];
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1422_11158.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1422_11158.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1422_11158.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___1422_11158.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let uu____11168 =
                      get_norm_request cfg (norm cfg' env []) args  in
                    match uu____11168 with
                    | FStar_Pervasives_Native.None  ->
                        (if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           FStar_Util.print_string "Norm request None ... \n"
                         else ();
                         (let stack1 =
                            FStar_All.pipe_right stack
                              (FStar_List.fold_right
                                 (fun uu____11204  ->
                                    fun stack1  ->
                                      match uu____11204 with
                                      | (a,aq) ->
                                          let uu____11216 =
                                            let uu____11217 =
                                              let uu____11224 =
                                                let uu____11225 =
                                                  let uu____11257 =
                                                    FStar_Util.mk_ref
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  (env, a, uu____11257,
                                                    false)
                                                   in
                                                Clos uu____11225  in
                                              (uu____11224, aq,
                                                (t1.FStar_Syntax_Syntax.pos))
                                               in
                                            Arg uu____11217  in
                                          uu____11216 :: stack1) args)
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____11325  ->
                               let uu____11326 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length args)
                                  in
                               FStar_Util.print1 "\tPushed %s arguments\n"
                                 uu____11326);
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
                            let uu____11358 =
                              let uu____11360 =
                                let uu____11362 =
                                  FStar_Util.time_diff start fin  in
                                FStar_Pervasives_Native.snd uu____11362  in
                              FStar_Util.string_of_int uu____11360  in
                            let uu____11369 =
                              FStar_Syntax_Print.term_to_string tm'  in
                            let uu____11371 =
                              FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                            let uu____11373 =
                              FStar_Syntax_Print.term_to_string tm_norm  in
                            FStar_Util.print4
                              "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                              uu____11358 uu____11369 uu____11371 uu____11373)
                         else ();
                         rebuild cfg env stack tm_norm)
                    | FStar_Pervasives_Native.Some (s,tm) ->
                        let delta_level =
                          let uu____11393 =
                            FStar_All.pipe_right s
                              (FStar_Util.for_some
                                 (fun uu___13_11400  ->
                                    match uu___13_11400 with
                                    | FStar_TypeChecker_Env.UnfoldUntil
                                        uu____11402 -> true
                                    | FStar_TypeChecker_Env.UnfoldOnly
                                        uu____11404 -> true
                                    | FStar_TypeChecker_Env.UnfoldFully
                                        uu____11408 -> true
                                    | uu____11412 -> false))
                             in
                          if uu____11393
                          then
                            [FStar_TypeChecker_Env.Unfold
                               FStar_Syntax_Syntax.delta_constant]
                          else [FStar_TypeChecker_Env.NoDelta]  in
                        let cfg'1 =
                          let uu___1462_11420 = cfg  in
                          let uu____11421 =
                            let uu___1464_11422 =
                              FStar_TypeChecker_Cfg.to_fsteps s  in
                            {
                              FStar_TypeChecker_Cfg.beta =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.beta);
                              FStar_TypeChecker_Cfg.iota =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.iota);
                              FStar_TypeChecker_Cfg.zeta =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.zeta);
                              FStar_TypeChecker_Cfg.weak =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.weak);
                              FStar_TypeChecker_Cfg.hnf =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.hnf);
                              FStar_TypeChecker_Cfg.primops =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.primops);
                              FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                              FStar_TypeChecker_Cfg.unfold_until =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.unfold_until);
                              FStar_TypeChecker_Cfg.unfold_only =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.unfold_only);
                              FStar_TypeChecker_Cfg.unfold_fully =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.unfold_fully);
                              FStar_TypeChecker_Cfg.unfold_attr =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.unfold_attr);
                              FStar_TypeChecker_Cfg.unfold_tac =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.unfold_tac);
                              FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                              FStar_TypeChecker_Cfg.simplify =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.simplify);
                              FStar_TypeChecker_Cfg.erase_universes =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.erase_universes);
                              FStar_TypeChecker_Cfg.allow_unbound_universes =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.allow_unbound_universes);
                              FStar_TypeChecker_Cfg.reify_ =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.reify_);
                              FStar_TypeChecker_Cfg.compress_uvars =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.compress_uvars);
                              FStar_TypeChecker_Cfg.no_full_norm =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.no_full_norm);
                              FStar_TypeChecker_Cfg.check_no_uvars =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.check_no_uvars);
                              FStar_TypeChecker_Cfg.unmeta =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.unmeta);
                              FStar_TypeChecker_Cfg.unascribe =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.unascribe);
                              FStar_TypeChecker_Cfg.in_full_norm_request =
                                true;
                              FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                              FStar_TypeChecker_Cfg.nbe_step =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.nbe_step);
                              FStar_TypeChecker_Cfg.for_extraction =
                                (uu___1464_11422.FStar_TypeChecker_Cfg.for_extraction)
                            }  in
                          {
                            FStar_TypeChecker_Cfg.steps = uu____11421;
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___1462_11420.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___1462_11420.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level = delta_level;
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___1462_11420.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___1462_11420.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___1462_11420.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                            FStar_TypeChecker_Cfg.reifying =
                              (uu___1462_11420.FStar_TypeChecker_Cfg.reifying)
                          }  in
                        let stack' =
                          let tail1 = (Cfg cfg) :: stack  in
                          if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                          then
                            let uu____11430 =
                              let uu____11431 =
                                let uu____11436 = FStar_Util.now ()  in
                                (tm, uu____11436)  in
                              Debug uu____11431  in
                            uu____11430 :: tail1
                          else tail1  in
                        norm cfg'1 env stack' tm))
              | FStar_Syntax_Syntax.Tm_type u ->
                  let u1 = norm_universe cfg env u  in
                  let uu____11441 =
                    mk (FStar_Syntax_Syntax.Tm_type u1)
                      t1.FStar_Syntax_Syntax.pos
                     in
                  rebuild cfg env stack uu____11441
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                  then norm cfg env stack t'
                  else
                    (let us1 =
                       let uu____11452 =
                         let uu____11459 =
                           FStar_List.map (norm_universe cfg env) us  in
                         (uu____11459, (t1.FStar_Syntax_Syntax.pos))  in
                       UnivArgs uu____11452  in
                     let stack1 = us1 :: stack  in norm cfg env stack1 t')
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____11468 = lookup_bvar env x  in
                  (match uu____11468 with
                   | Univ uu____11469 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> failwith "Term variable not found"
                   | Clos (env1,t0,r,fix) ->
                       if
                         (Prims.op_Negation fix) ||
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                       then
                         let uu____11523 = FStar_ST.op_Bang r  in
                         (match uu____11523 with
                          | FStar_Pervasives_Native.Some (env2,t') ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11619  ->
                                    let uu____11620 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____11622 =
                                      FStar_Syntax_Print.term_to_string t'
                                       in
                                    FStar_Util.print2
                                      "Lazy hit: %s cached to %s\n"
                                      uu____11620 uu____11622);
                               (let uu____11625 = maybe_weakly_reduced t'  in
                                if uu____11625
                                then
                                  match stack with
                                  | [] when
                                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                        ||
                                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                      -> rebuild cfg env2 stack t'
                                  | uu____11628 -> norm cfg env2 stack t'
                                else rebuild cfg env2 stack t'))
                          | FStar_Pervasives_Native.None  ->
                              norm cfg env1 ((MemoLazy r) :: stack) t0)
                       else norm cfg env1 stack t0)
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  (match stack with
                   | (UnivArgs uu____11672)::uu____11673 ->
                       failwith
                         "Ill-typed term: universes cannot be applied to term abstraction"
                   | (Arg (c,uu____11684,uu____11685))::stack_rest ->
                       (match c with
                        | Univ uu____11689 ->
                            norm cfg ((FStar_Pervasives_Native.None, c) ::
                              env) stack_rest t1
                        | uu____11698 ->
                            (match bs with
                             | [] -> failwith "Impossible"
                             | b::[] ->
                                 (FStar_TypeChecker_Cfg.log cfg
                                    (fun uu____11728  ->
                                       let uu____11729 = closure_to_string c
                                          in
                                       FStar_Util.print1 "\tShifted %s\n"
                                         uu____11729);
                                  norm cfg
                                    (((FStar_Pervasives_Native.Some b), c) ::
                                    env) stack_rest body)
                             | b::tl1 ->
                                 (FStar_TypeChecker_Cfg.log cfg
                                    (fun uu____11765  ->
                                       let uu____11766 = closure_to_string c
                                          in
                                       FStar_Util.print1 "\tShifted %s\n"
                                         uu____11766);
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
                          (fun uu____11814  ->
                             let uu____11815 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.print1 "\tSet memo %s\n" uu____11815);
                        norm cfg env stack1 t1)
                   | (Match uu____11818)::uu____11819 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____11834 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____11834 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____11870  -> dummy :: env1)
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
                                             let uu____11914 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____11914)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1582_11922 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1582_11922.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1582_11922.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____11923 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11929  ->
                                    let uu____11930 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____11930);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1589_11945 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1589_11945.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1589_11945.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1589_11945.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1589_11945.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1589_11945.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1589_11945.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1589_11945.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1589_11945.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Debug uu____11949)::uu____11950 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____11961 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____11961 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____11997  -> dummy :: env1)
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
                                             let uu____12041 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12041)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1582_12049 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1582_12049.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1582_12049.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12050 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12056  ->
                                    let uu____12057 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12057);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1589_12072 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1589_12072.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1589_12072.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1589_12072.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1589_12072.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1589_12072.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1589_12072.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1589_12072.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1589_12072.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Meta uu____12076)::uu____12077 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12090 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12090 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12126  -> dummy :: env1)
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
                                             let uu____12170 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12170)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1582_12178 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1582_12178.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1582_12178.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12179 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12185  ->
                                    let uu____12186 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12186);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1589_12201 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1589_12201.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1589_12201.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1589_12201.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1589_12201.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1589_12201.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1589_12201.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1589_12201.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1589_12201.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Let uu____12205)::uu____12206 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12221 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12221 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12257  -> dummy :: env1)
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
                                             let uu____12301 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12301)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1582_12309 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1582_12309.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1582_12309.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12310 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12316  ->
                                    let uu____12317 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12317);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1589_12332 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1589_12332.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1589_12332.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1589_12332.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1589_12332.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1589_12332.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1589_12332.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1589_12332.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1589_12332.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (App uu____12336)::uu____12337 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12352 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12352 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12388  -> dummy :: env1)
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
                                             let uu____12432 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12432)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1582_12440 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1582_12440.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1582_12440.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12441 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12447  ->
                                    let uu____12448 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12448);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1589_12463 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1589_12463.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1589_12463.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1589_12463.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1589_12463.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1589_12463.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1589_12463.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1589_12463.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1589_12463.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Abs uu____12467)::uu____12468 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12487 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12487 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12523  -> dummy :: env1)
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
                                             let uu____12567 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12567)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1582_12575 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1582_12575.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1582_12575.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12576 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12582  ->
                                    let uu____12583 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12583);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1589_12598 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1589_12598.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1589_12598.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1589_12598.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1589_12598.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1589_12598.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1589_12598.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1589_12598.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1589_12598.FStar_TypeChecker_Cfg.reifying)
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
                         (let uu____12606 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12606 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12642  -> dummy :: env1)
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
                                             let uu____12686 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12686)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1582_12694 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1582_12694.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1582_12694.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12695 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12701  ->
                                    let uu____12702 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12702);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1589_12717 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1589_12717.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1589_12717.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1589_12717.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1589_12717.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1589_12717.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1589_12717.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1589_12717.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1589_12717.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1))))
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let strict_args =
                    let uu____12753 =
                      let uu____12754 = FStar_Syntax_Util.un_uinst head1  in
                      uu____12754.FStar_Syntax_Syntax.n  in
                    match uu____12753 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_TypeChecker_Env.fv_has_strict_args
                          cfg.FStar_TypeChecker_Cfg.tcenv fv
                    | uu____12763 -> FStar_Pervasives_Native.None  in
                  (match strict_args with
                   | FStar_Pervasives_Native.None  ->
                       let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____12784  ->
                                 fun stack1  ->
                                   match uu____12784 with
                                   | (a,aq) ->
                                       let uu____12796 =
                                         let uu____12797 =
                                           let uu____12804 =
                                             let uu____12805 =
                                               let uu____12837 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____12837, false)
                                                in
                                             Clos uu____12805  in
                                           (uu____12804, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____12797  in
                                       uu____12796 :: stack1) args)
                          in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____12905  ->
                             let uu____12906 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length args)
                                in
                             FStar_Util.print1 "\tPushed %s arguments\n"
                               uu____12906);
                        norm cfg env stack1 head1)
                   | FStar_Pervasives_Native.Some strict_args1 ->
                       let norm_args =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____12957  ->
                                 match uu____12957 with
                                 | (a,i) ->
                                     let uu____12968 = norm cfg env [] a  in
                                     (uu____12968, i)))
                          in
                       let norm_args_len = FStar_List.length norm_args  in
                       let uu____12974 =
                         FStar_All.pipe_right strict_args1
                           (FStar_List.for_all
                              (fun i  ->
                                 if i >= norm_args_len
                                 then false
                                 else
                                   (let uu____12989 =
                                      FStar_List.nth norm_args i  in
                                    match uu____12989 with
                                    | (arg_i,uu____13000) ->
                                        let uu____13001 =
                                          FStar_Syntax_Util.head_and_args
                                            arg_i
                                           in
                                        (match uu____13001 with
                                         | (head2,uu____13020) ->
                                             let uu____13045 =
                                               let uu____13046 =
                                                 FStar_Syntax_Util.un_uinst
                                                   head2
                                                  in
                                               uu____13046.FStar_Syntax_Syntax.n
                                                in
                                             (match uu____13045 with
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____13050 -> true
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv ->
                                                  let uu____13053 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Env.is_datacon
                                                    cfg.FStar_TypeChecker_Cfg.tcenv
                                                    uu____13053
                                              | uu____13054 -> false)))))
                          in
                       if uu____12974
                       then
                         let stack1 =
                           FStar_All.pipe_right stack
                             (FStar_List.fold_right
                                (fun uu____13071  ->
                                   fun stack1  ->
                                     match uu____13071 with
                                     | (a,aq) ->
                                         let uu____13083 =
                                           let uu____13084 =
                                             let uu____13091 =
                                               let uu____13092 =
                                                 let uu____13124 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], a))
                                                    in
                                                 (env, a, uu____13124, false)
                                                  in
                                               Clos uu____13092  in
                                             (uu____13091, aq,
                                               (t1.FStar_Syntax_Syntax.pos))
                                              in
                                           Arg uu____13084  in
                                         uu____13083 :: stack1) norm_args)
                            in
                         (FStar_TypeChecker_Cfg.log cfg
                            (fun uu____13206  ->
                               let uu____13207 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length args)
                                  in
                               FStar_Util.print1 "\tPushed %s arguments\n"
                                 uu____13207);
                          norm cfg env stack1 head1)
                       else
                         (let head2 = closure_as_term cfg env head1  in
                          let term =
                            FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                              FStar_Pervasives_Native.None
                              t1.FStar_Syntax_Syntax.pos
                             in
                          rebuild cfg env stack term))
              | FStar_Syntax_Syntax.Tm_refine (x,uu____13227) when
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
                                ((let uu___1651_13272 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1651_13272.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1651_13272.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t_x
                                  }), f)) t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild cfg env stack t2
                     | uu____13273 ->
                         let uu____13288 = closure_as_term cfg env t1  in
                         rebuild cfg env stack uu____13288)
                  else
                    (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                     let uu____13292 =
                       FStar_Syntax_Subst.open_term
                         [(x, FStar_Pervasives_Native.None)] f
                        in
                     match uu____13292 with
                     | (closing,f1) ->
                         let f2 = norm cfg (dummy :: env) [] f1  in
                         let t2 =
                           let uu____13323 =
                             let uu____13324 =
                               let uu____13331 =
                                 FStar_Syntax_Subst.close closing f2  in
                               ((let uu___1660_13337 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1660_13337.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1660_13337.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t_x
                                 }), uu____13331)
                                in
                             FStar_Syntax_Syntax.Tm_refine uu____13324  in
                           mk uu____13323 t1.FStar_Syntax_Syntax.pos  in
                         rebuild cfg env stack t2)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                  then
                    let uu____13361 = closure_as_term cfg env t1  in
                    rebuild cfg env stack uu____13361
                  else
                    (let uu____13364 = FStar_Syntax_Subst.open_comp bs c  in
                     match uu____13364 with
                     | (bs1,c1) ->
                         let c2 =
                           let uu____13372 =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13398  -> dummy :: env1) env)
                              in
                           norm_comp cfg uu____13372 c1  in
                         let t2 =
                           let uu____13422 = norm_binders cfg env bs1  in
                           FStar_Syntax_Util.arrow uu____13422 c2  in
                         rebuild cfg env stack t2)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
                  -> norm cfg env stack t11
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
                  (match stack with
                   | (Match uu____13535)::uu____13536 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13549  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (Arg uu____13551)::uu____13552 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13563  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (App
                       (uu____13565,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_reify );
                                      FStar_Syntax_Syntax.pos = uu____13566;
                                      FStar_Syntax_Syntax.vars = uu____13567;_},uu____13568,uu____13569))::uu____13570
                       when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13577  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (MemoLazy uu____13579)::uu____13580 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13591  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | uu____13593 ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13596  ->
                             FStar_Util.print_string
                               "+++ Keeping ascription \n");
                        (let t12 = norm cfg env [] t11  in
                         FStar_TypeChecker_Cfg.log cfg
                           (fun uu____13601  ->
                              FStar_Util.print_string
                                "+++ Normalizing ascription \n");
                         (let tc1 =
                            match tc with
                            | FStar_Util.Inl t2 ->
                                let uu____13627 = norm cfg env [] t2  in
                                FStar_Util.Inl uu____13627
                            | FStar_Util.Inr c ->
                                let uu____13641 = norm_comp cfg env c  in
                                FStar_Util.Inr uu____13641
                             in
                          let tacopt1 =
                            FStar_Util.map_opt tacopt (norm cfg env [])  in
                          match stack with
                          | (Cfg cfg1)::stack1 ->
                              let t2 =
                                let uu____13664 =
                                  let uu____13665 =
                                    let uu____13692 =
                                      FStar_Syntax_Util.unascribe t12  in
                                    (uu____13692, (tc1, tacopt1), l)  in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____13665
                                   in
                                mk uu____13664 t1.FStar_Syntax_Syntax.pos  in
                              norm cfg1 env stack1 t2
                          | uu____13727 ->
                              let uu____13728 =
                                let uu____13729 =
                                  let uu____13730 =
                                    let uu____13757 =
                                      FStar_Syntax_Util.unascribe t12  in
                                    (uu____13757, (tc1, tacopt1), l)  in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____13730
                                   in
                                mk uu____13729 t1.FStar_Syntax_Syntax.pos  in
                              rebuild cfg env stack uu____13728))))
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
                      let uu___1739_13835 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (let uu___1741_13838 =
                             cfg.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak = true;
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1741_13838.FStar_TypeChecker_Cfg.for_extraction)
                           });
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1739_13835.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1739_13835.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___1739_13835.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1739_13835.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1739_13835.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1739_13835.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___1739_13835.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___1739_13835.FStar_TypeChecker_Cfg.reifying)
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
                            let uu____13879 =
                              FStar_Syntax_Subst.univ_var_opening
                                lb.FStar_Syntax_Syntax.lbunivs
                               in
                            match uu____13879 with
                            | (openings,lbunivs) ->
                                let cfg1 =
                                  let uu___1754_13899 = cfg  in
                                  let uu____13900 =
                                    FStar_TypeChecker_Env.push_univ_vars
                                      cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                     in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1754_13899.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv = uu____13900;
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1754_13899.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1754_13899.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1754_13899.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong =
                                      (uu___1754_13899.FStar_TypeChecker_Cfg.strong);
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1754_13899.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1754_13899.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1754_13899.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                let norm1 t2 =
                                  let uu____13907 =
                                    let uu____13908 =
                                      FStar_Syntax_Subst.subst openings t2
                                       in
                                    norm cfg1 env [] uu____13908  in
                                  FStar_Syntax_Subst.close_univ_vars lbunivs
                                    uu____13907
                                   in
                                let lbtyp =
                                  norm1 lb.FStar_Syntax_Syntax.lbtyp  in
                                let lbdef =
                                  norm1 lb.FStar_Syntax_Syntax.lbdef  in
                                let uu___1761_13911 = lb  in
                                {
                                  FStar_Syntax_Syntax.lbname =
                                    (uu___1761_13911.FStar_Syntax_Syntax.lbname);
                                  FStar_Syntax_Syntax.lbunivs = lbunivs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1761_13911.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = lbdef;
                                  FStar_Syntax_Syntax.lbattrs =
                                    (uu___1761_13911.FStar_Syntax_Syntax.lbattrs);
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1761_13911.FStar_Syntax_Syntax.lbpos)
                                }))
                     in
                  let uu____13912 =
                    mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                      t1.FStar_Syntax_Syntax.pos
                     in
                  rebuild cfg env stack uu____13912
              | FStar_Syntax_Syntax.Tm_let
                  ((uu____13925,{
                                  FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                    uu____13926;
                                  FStar_Syntax_Syntax.lbunivs = uu____13927;
                                  FStar_Syntax_Syntax.lbtyp = uu____13928;
                                  FStar_Syntax_Syntax.lbeff = uu____13929;
                                  FStar_Syntax_Syntax.lbdef = uu____13930;
                                  FStar_Syntax_Syntax.lbattrs = uu____13931;
                                  FStar_Syntax_Syntax.lbpos = uu____13932;_}::uu____13933),uu____13934)
                  -> rebuild cfg env stack t1
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let uu____13979 =
                    FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
                  if uu____13979
                  then
                    let binder =
                      let uu____13983 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.mk_binder uu____13983  in
                    let env1 =
                      let uu____13993 =
                        let uu____14000 =
                          let uu____14001 =
                            let uu____14033 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env, (lb.FStar_Syntax_Syntax.lbdef),
                              uu____14033, false)
                             in
                          Clos uu____14001  in
                        ((FStar_Pervasives_Native.Some binder), uu____14000)
                         in
                      uu____13993 :: env  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____14108  ->
                          FStar_Util.print_string "+++ Reducing Tm_let\n");
                     norm cfg env1 stack body)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____14115  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____14117 = closure_as_term cfg env t1  in
                        rebuild cfg env stack uu____14117))
                    else
                      (let uu____14120 =
                         let uu____14125 =
                           let uu____14126 =
                             let uu____14133 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____14133
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____14126]  in
                         FStar_Syntax_Subst.open_term uu____14125 body  in
                       match uu____14120 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____14160  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____14169 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____14169  in
                               FStar_Util.Inl
                                 (let uu___1802_14185 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1802_14185.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1802_14185.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____14188  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1807_14191 = lb  in
                                let uu____14192 =
                                  norm cfg env []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____14195 =
                                  FStar_List.map (norm cfg env [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1807_14191.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1807_14191.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____14192;
                                  FStar_Syntax_Syntax.lbattrs = uu____14195;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1807_14191.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____14230  -> dummy :: env1)
                                     env)
                                 in
                              let stack1 = (Cfg cfg) :: stack  in
                              let cfg1 =
                                let uu___1814_14255 = cfg  in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1814_14255.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1814_14255.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1814_14255.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1814_14255.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1814_14255.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1814_14255.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1814_14255.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1814_14255.FStar_TypeChecker_Cfg.reifying)
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____14259  ->
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
                  let uu____14280 = FStar_Syntax_Subst.open_let_rec lbs body
                     in
                  (match uu____14280 with
                   | (lbs1,body1) ->
                       let lbs2 =
                         FStar_List.map
                           (fun lb  ->
                              let ty =
                                norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                 in
                              let lbname =
                                let uu____14316 =
                                  let uu___1830_14317 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1830_14317.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1830_14317.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  }  in
                                FStar_Util.Inl uu____14316  in
                              let uu____14318 =
                                FStar_Syntax_Util.abs_formals
                                  lb.FStar_Syntax_Syntax.lbdef
                                 in
                              match uu____14318 with
                              | (xs,def_body,lopt) ->
                                  let xs1 = norm_binders cfg env xs  in
                                  let env1 =
                                    let uu____14344 =
                                      FStar_List.map
                                        (fun uu____14366  -> dummy) xs1
                                       in
                                    let uu____14373 =
                                      let uu____14382 =
                                        FStar_List.map
                                          (fun uu____14398  -> dummy) lbs1
                                         in
                                      FStar_List.append uu____14382 env  in
                                    FStar_List.append uu____14344 uu____14373
                                     in
                                  let def_body1 = norm cfg env1 [] def_body
                                     in
                                  let lopt1 =
                                    match lopt with
                                    | FStar_Pervasives_Native.Some rc ->
                                        let uu____14418 =
                                          let uu___1844_14419 = rc  in
                                          let uu____14420 =
                                            FStar_Util.map_opt
                                              rc.FStar_Syntax_Syntax.residual_typ
                                              (norm cfg env1 [])
                                             in
                                          {
                                            FStar_Syntax_Syntax.residual_effect
                                              =
                                              (uu___1844_14419.FStar_Syntax_Syntax.residual_effect);
                                            FStar_Syntax_Syntax.residual_typ
                                              = uu____14420;
                                            FStar_Syntax_Syntax.residual_flags
                                              =
                                              (uu___1844_14419.FStar_Syntax_Syntax.residual_flags)
                                          }  in
                                        FStar_Pervasives_Native.Some
                                          uu____14418
                                    | uu____14429 -> lopt  in
                                  let def =
                                    FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                     in
                                  let uu___1849_14435 = lb  in
                                  {
                                    FStar_Syntax_Syntax.lbname = lbname;
                                    FStar_Syntax_Syntax.lbunivs =
                                      (uu___1849_14435.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp = ty;
                                    FStar_Syntax_Syntax.lbeff =
                                      (uu___1849_14435.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs =
                                      (uu___1849_14435.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (uu___1849_14435.FStar_Syntax_Syntax.lbpos)
                                  }) lbs1
                          in
                       let env' =
                         let uu____14445 =
                           FStar_List.map (fun uu____14461  -> dummy) lbs2
                            in
                         FStar_List.append uu____14445 env  in
                       let body2 = norm cfg env' [] body1  in
                       let uu____14469 =
                         FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                       (match uu____14469 with
                        | (lbs3,body3) ->
                            let t2 =
                              let uu___1858_14485 = t1  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_let
                                     ((true, lbs3), body3));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1858_14485.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1858_14485.FStar_Syntax_Syntax.vars)
                              }  in
                            rebuild cfg env stack t2))
              | FStar_Syntax_Syntax.Tm_let (lbs,body) when
                  Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                  ->
                  let uu____14519 = closure_as_term cfg env t1  in
                  rebuild cfg env stack uu____14519
              | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
                  let uu____14540 =
                    FStar_List.fold_right
                      (fun lb  ->
                         fun uu____14618  ->
                           match uu____14618 with
                           | (rec_env,memos,i) ->
                               let bv =
                                 let uu___1874_14743 =
                                   FStar_Util.left
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1874_14743.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index = i;
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1874_14743.FStar_Syntax_Syntax.sort)
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
                  (match uu____14540 with
                   | (rec_env,memos,uu____14934) ->
                       let uu____14989 =
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
                                let uu____15238 =
                                  let uu____15245 =
                                    let uu____15246 =
                                      let uu____15278 =
                                        FStar_Util.mk_ref
                                          FStar_Pervasives_Native.None
                                         in
                                      (rec_env,
                                        (lb.FStar_Syntax_Syntax.lbdef),
                                        uu____15278, false)
                                       in
                                    Clos uu____15246  in
                                  (FStar_Pervasives_Native.None, uu____15245)
                                   in
                                uu____15238 :: env1)
                           (FStar_Pervasives_Native.snd lbs) env
                          in
                       norm cfg body_env stack body)
              | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____15363  ->
                        let uu____15364 =
                          FStar_Syntax_Print.metadata_to_string m  in
                        FStar_Util.print1 ">> metadata = %s\n" uu____15364);
                   (match m with
                    | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                        reduce_impure_comp cfg env stack head1
                          (FStar_Util.Inl m1) t2
                    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                        reduce_impure_comp cfg env stack head1
                          (FStar_Util.Inr (m1, m')) t2
                    | uu____15388 ->
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                        then norm cfg env stack head1
                        else
                          (match stack with
                           | uu____15392::uu____15393 ->
                               (match m with
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (l,r,uu____15398) ->
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
                                | uu____15477 -> norm cfg env stack head1)
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
                                     let uu____15525 =
                                       let uu____15546 =
                                         norm_pattern_args cfg env args  in
                                       (names2, uu____15546)  in
                                     FStar_Syntax_Syntax.Meta_pattern
                                       uu____15525
                                 | uu____15575 -> m  in
                               let t2 =
                                 mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                   t1.FStar_Syntax_Syntax.pos
                                  in
                               rebuild cfg env stack t2)))
              | FStar_Syntax_Syntax.Tm_delayed uu____15581 ->
                  let t2 = FStar_Syntax_Subst.compress t1  in
                  norm cfg env stack t2
              | FStar_Syntax_Syntax.Tm_uvar uu____15605 ->
                  let t2 = FStar_Syntax_Subst.compress t1  in
                  (match t2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar uu____15619 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                       then
                         let uu____15633 =
                           let uu____15635 =
                             FStar_Range.string_of_range
                               t2.FStar_Syntax_Syntax.pos
                              in
                           let uu____15637 =
                             FStar_Syntax_Print.term_to_string t2  in
                           FStar_Util.format2
                             "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                             uu____15635 uu____15637
                            in
                         failwith uu____15633
                       else
                         (let uu____15642 = inline_closure_env cfg env [] t2
                             in
                          rebuild cfg env stack uu____15642)
                   | uu____15643 -> norm cfg env stack t2)))

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
              let uu____15652 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____15652 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____15666  ->
                        let uu____15667 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____15667);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____15680  ->
                        let uu____15681 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____15683 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____15681 uu____15683);
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
                      | (UnivArgs (us',uu____15696))::stack1 ->
                          ((let uu____15705 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____15705
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____15713 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____15713) us'
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
                      | uu____15749 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____15752 ->
                          let uu____15755 =
                            let uu____15757 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____15757
                             in
                          failwith uu____15755
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
                  let uu___1986_15785 = cfg  in
                  let uu____15786 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____15786;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1986_15785.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1986_15785.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1986_15785.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1986_15785.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1986_15785.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1986_15785.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1986_15785.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____15817,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____15818;
                                    FStar_Syntax_Syntax.vars = uu____15819;_},uu____15820,uu____15821))::uu____15822
                     -> ()
                 | uu____15827 ->
                     let uu____15830 =
                       let uu____15832 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____15832
                        in
                     failwith uu____15830);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____15841  ->
                      let uu____15842 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____15844 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____15842
                        uu____15844);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____15848 =
                    let uu____15849 = FStar_Syntax_Subst.compress head3  in
                    uu____15849.FStar_Syntax_Syntax.n  in
                  match uu____15848 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____15870 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____15870
                         in
                      let uu____15871 =
                        let uu____15880 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_bind_repr
                           in
                        FStar_All.pipe_right uu____15880 FStar_Util.must  in
                      (match uu____15871 with
                       | (uu____15895,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____15905 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____15916 =
                                    let uu____15917 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____15917.FStar_Syntax_Syntax.n  in
                                  match uu____15916 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____15923,uu____15924))
                                      ->
                                      let uu____15933 =
                                        let uu____15934 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____15934.FStar_Syntax_Syntax.n  in
                                      (match uu____15933 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____15940,msrc,uu____15942))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____15951 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____15951
                                       | uu____15952 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____15953 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____15954 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____15954 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___2058_15959 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___2058_15959.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___2058_15959.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___2058_15959.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___2058_15959.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___2058_15959.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____15960 = FStar_List.tl stack
                                        in
                                     let uu____15961 =
                                       let uu____15962 =
                                         let uu____15969 =
                                           let uu____15970 =
                                             let uu____15984 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____15984)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____15970
                                            in
                                         FStar_Syntax_Syntax.mk uu____15969
                                          in
                                       uu____15962
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____15960 uu____15961
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____16000 =
                                       let uu____16002 = is_return body  in
                                       match uu____16002 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____16007;
                                             FStar_Syntax_Syntax.vars =
                                               uu____16008;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____16011 -> false  in
                                     if uu____16000
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
                                          let uu____16035 =
                                            let uu____16042 =
                                              let uu____16043 =
                                                let uu____16062 =
                                                  let uu____16071 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____16071]  in
                                                (uu____16062, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____16043
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____16042
                                             in
                                          uu____16035
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____16110 =
                                            let uu____16111 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____16111.FStar_Syntax_Syntax.n
                                             in
                                          match uu____16110 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____16117::uu____16118::[])
                                              ->
                                              let uu____16123 =
                                                let uu____16130 =
                                                  let uu____16131 =
                                                    let uu____16138 =
                                                      let uu____16139 =
                                                        let uu____16140 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____16140
                                                         in
                                                      let uu____16141 =
                                                        let uu____16144 =
                                                          let uu____16145 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____16145
                                                           in
                                                        [uu____16144]  in
                                                      uu____16139 ::
                                                        uu____16141
                                                       in
                                                    (bind1, uu____16138)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____16131
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____16130
                                                 in
                                              uu____16123
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____16148 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____16163 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____16163
                                          then
                                            let uu____16176 =
                                              let uu____16185 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____16185
                                               in
                                            let uu____16186 =
                                              let uu____16197 =
                                                let uu____16206 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____16206
                                                 in
                                              [uu____16197]  in
                                            uu____16176 :: uu____16186
                                          else []  in
                                        let reified =
                                          let args =
                                            let uu____16255 =
                                              FStar_Syntax_Util.is_layered ed
                                               in
                                            if uu____16255
                                            then
                                              let unit_args =
                                                let uu____16279 =
                                                  let uu____16280 =
                                                    let uu____16283 =
                                                      let uu____16284 =
                                                        FStar_All.pipe_right
                                                          ed
                                                          FStar_Syntax_Util.get_bind_vc_combinator
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____16284
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____16283
                                                      FStar_Syntax_Subst.compress
                                                     in
                                                  uu____16280.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____16279 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (uu____16325::uu____16326::bs,uu____16328)
                                                    when
                                                    (FStar_List.length bs) >=
                                                      (Prims.of_int (2))
                                                    ->
                                                    let uu____16380 =
                                                      let uu____16389 =
                                                        FStar_All.pipe_right
                                                          bs
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs)
                                                                -
                                                                (Prims.of_int (2))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____16389
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____16380
                                                      (FStar_List.map
                                                         (fun uu____16520  ->
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.unit_const))
                                                | uu____16527 ->
                                                    let uu____16528 =
                                                      let uu____16534 =
                                                        let uu____16536 =
                                                          FStar_Ident.string_of_lid
                                                            ed.FStar_Syntax_Syntax.mname
                                                           in
                                                        let uu____16538 =
                                                          let uu____16540 =
                                                            let uu____16541 =
                                                              FStar_All.pipe_right
                                                                ed
                                                                FStar_Syntax_Util.get_bind_vc_combinator
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____16541
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____16540
                                                            FStar_Syntax_Print.term_to_string
                                                           in
                                                        FStar_Util.format2
                                                          "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                          uu____16536
                                                          uu____16538
                                                         in
                                                      (FStar_Errors.Fatal_UnexpectedEffect,
                                                        uu____16534)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____16528 rng
                                                 in
                                              let uu____16575 =
                                                FStar_Syntax_Syntax.as_arg
                                                  lb.FStar_Syntax_Syntax.lbtyp
                                                 in
                                              let uu____16584 =
                                                let uu____16595 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____16604 =
                                                  let uu____16615 =
                                                    let uu____16626 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head4
                                                       in
                                                    let uu____16635 =
                                                      let uu____16646 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          body2
                                                         in
                                                      [uu____16646]  in
                                                    uu____16626 ::
                                                      uu____16635
                                                     in
                                                  FStar_List.append unit_args
                                                    uu____16615
                                                   in
                                                uu____16595 :: uu____16604
                                                 in
                                              uu____16575 :: uu____16584
                                            else
                                              (let uu____16705 =
                                                 let uu____16716 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____16725 =
                                                   let uu____16736 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   [uu____16736]  in
                                                 uu____16716 :: uu____16725
                                                  in
                                               let uu____16769 =
                                                 let uu____16780 =
                                                   let uu____16791 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       FStar_Syntax_Syntax.tun
                                                      in
                                                   let uu____16800 =
                                                     let uu____16811 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         head4
                                                        in
                                                     let uu____16820 =
                                                       let uu____16831 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let uu____16840 =
                                                         let uu____16851 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2
                                                            in
                                                         [uu____16851]  in
                                                       uu____16831 ::
                                                         uu____16840
                                                        in
                                                     uu____16811 ::
                                                       uu____16820
                                                      in
                                                   uu____16791 :: uu____16800
                                                    in
                                                 FStar_List.append
                                                   maybe_range_arg
                                                   uu____16780
                                                  in
                                               FStar_List.append uu____16705
                                                 uu____16769)
                                             in
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (bind_inst, args))
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____16932  ->
                                             let uu____16933 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____16935 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____16933 uu____16935);
                                        (let uu____16938 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____16938 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____16966 = FStar_Options.defensive ()  in
                        if uu____16966
                        then
                          let is_arg_impure uu____16981 =
                            match uu____16981 with
                            | (e,q) ->
                                let uu____16995 =
                                  let uu____16996 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16996.FStar_Syntax_Syntax.n  in
                                (match uu____16995 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____17012 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____17012
                                 | uu____17014 -> false)
                             in
                          let uu____17016 =
                            let uu____17018 =
                              let uu____17029 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____17029 :: args  in
                            FStar_Util.for_some is_arg_impure uu____17018  in
                          (if uu____17016
                           then
                             let uu____17055 =
                               let uu____17061 =
                                 let uu____17063 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____17063
                                  in
                               (FStar_Errors.Warning_Defensive, uu____17061)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____17055
                           else ())
                        else ());
                       (let fallback1 uu____17076 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____17080  ->
                               let uu____17081 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____17081 "");
                          (let uu____17085 = FStar_List.tl stack  in
                           let uu____17086 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____17085 uu____17086)
                           in
                        let fallback2 uu____17092 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____17096  ->
                               let uu____17097 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____17097 "");
                          (let uu____17101 = FStar_List.tl stack  in
                           let uu____17102 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____17101 uu____17102)
                           in
                        let uu____17107 =
                          let uu____17108 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____17108.FStar_Syntax_Syntax.n  in
                        match uu____17107 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____17114 =
                              let uu____17116 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____17116  in
                            if uu____17114
                            then fallback1 ()
                            else
                              (let uu____17121 =
                                 let uu____17123 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____17123  in
                               if uu____17121
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____17140 =
                                      let uu____17145 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____17145 args
                                       in
                                    uu____17140 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____17146 = FStar_List.tl stack  in
                                  norm cfg env uu____17146 t1))
                        | uu____17147 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____17149) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____17173 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____17173  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____17177  ->
                            let uu____17178 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____17178);
                       (let uu____17181 = FStar_List.tl stack  in
                        norm cfg env uu____17181 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____17302  ->
                                match uu____17302 with
                                | (pat,wopt,tm) ->
                                    let uu____17350 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____17350)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____17382 = FStar_List.tl stack  in
                      norm cfg env uu____17382 tm
                  | uu____17383 -> fallback ()))

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
              (fun uu____17397  ->
                 let uu____17398 = FStar_Ident.string_of_lid msrc  in
                 let uu____17400 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17402 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17398
                   uu____17400 uu____17402);
            (let uu____17405 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____17408 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env)
                     in
                  Prims.op_Negation uu____17408)
                in
             if uu____17405
             then
               let ed =
                 let uu____17413 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17413  in
               let uu____17414 =
                 let uu____17421 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr
                    in
                 FStar_All.pipe_right uu____17421 FStar_Util.must  in
               match uu____17414 with
               | (uu____17458,return_repr) ->
                   let return_inst =
                     let uu____17467 =
                       let uu____17468 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17468.FStar_Syntax_Syntax.n  in
                     match uu____17467 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17474::[]) ->
                         let uu____17479 =
                           let uu____17486 =
                             let uu____17487 =
                               let uu____17494 =
                                 let uu____17495 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17495]  in
                               (return_tm, uu____17494)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17487  in
                           FStar_Syntax_Syntax.mk uu____17486  in
                         uu____17479 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17498 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17502 =
                     let uu____17509 =
                       let uu____17510 =
                         let uu____17527 =
                           let uu____17538 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17547 =
                             let uu____17558 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17558]  in
                           uu____17538 :: uu____17547  in
                         (return_inst, uu____17527)  in
                       FStar_Syntax_Syntax.Tm_app uu____17510  in
                     FStar_Syntax_Syntax.mk uu____17509  in
                   uu____17502 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17605 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17605 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17608 =
                      let uu____17610 = FStar_Ident.text_of_lid msrc  in
                      let uu____17612 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17610 uu____17612
                       in
                    failwith uu____17608
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17615;
                      FStar_TypeChecker_Env.mtarget = uu____17616;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17617;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17637 =
                      let uu____17639 = FStar_Ident.text_of_lid msrc  in
                      let uu____17641 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17639 uu____17641
                       in
                    failwith uu____17637
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17644;
                      FStar_TypeChecker_Env.mtarget = uu____17645;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17646;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____17677 =
                        FStar_TypeChecker_Env.is_reifiable_effect env msrc
                         in
                      if uu____17677
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____17682 =
                           let uu____17689 =
                             let uu____17690 =
                               let uu____17709 =
                                 let uu____17718 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____17718]  in
                               (uu____17709, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____17690  in
                           FStar_Syntax_Syntax.mk uu____17689  in
                         uu____17682 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____17751 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    lift uu____17751 t e1))

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
                (fun uu____17821  ->
                   match uu____17821 with
                   | (a,imp) ->
                       let uu____17840 = norm cfg env [] a  in
                       (uu____17840, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17850  ->
             let uu____17851 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17853 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17851 uu____17853);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17879 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17882  -> FStar_Pervasives_Native.Some _17882)
                     uu____17879
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2223_17883 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2223_17883.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2223_17883.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17905 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17908  -> FStar_Pervasives_Native.Some _17908)
                     uu____17905
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2234_17909 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2234_17909.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2234_17909.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17954  ->
                      match uu____17954 with
                      | (a,i) ->
                          let uu____17974 = norm cfg env [] a  in
                          (uu____17974, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17996  ->
                       match uu___14_17996 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____18000 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____18000
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2251_18008 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2253_18011 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2253_18011.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2251_18008.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2251_18008.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____18015 = b  in
        match uu____18015 with
        | (x,imp) ->
            let x1 =
              let uu___2261_18023 = x  in
              let uu____18024 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2261_18023.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2261_18023.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____18024
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____18035 =
                    let uu____18036 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____18036  in
                  FStar_Pervasives_Native.Some uu____18035
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____18047 =
          FStar_List.fold_left
            (fun uu____18081  ->
               fun b  ->
                 match uu____18081 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____18047 with | (nbs,uu____18161) -> FStar_List.rev nbs

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
            let uu____18193 =
              let uu___2286_18194 = rc  in
              let uu____18195 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2286_18194.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____18195;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2286_18194.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____18193
        | uu____18213 -> lopt

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
            (let uu____18223 = FStar_Syntax_Print.term_to_string tm  in
             let uu____18225 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____18223 uu____18225)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_18237  ->
      match uu___15_18237 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____18250 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____18250 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____18254 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____18254)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____18262 = norm_cb cfg  in
            reduce_primops uu____18262 cfg env tm  in
          let uu____18267 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____18267
          then tm1
          else
            (let w t =
               let uu___2315_18286 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2315_18286.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2315_18286.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____18298 =
                 let uu____18299 = FStar_Syntax_Util.unmeta t  in
                 uu____18299.FStar_Syntax_Syntax.n  in
               match uu____18298 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____18311 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18375)::args1,(bv,uu____18378)::bs1) ->
                   let uu____18432 =
                     let uu____18433 = FStar_Syntax_Subst.compress t  in
                     uu____18433.FStar_Syntax_Syntax.n  in
                   (match uu____18432 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18438 -> false)
               | ([],[]) -> true
               | (uu____18469,uu____18470) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18521 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18523 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18521
                    uu____18523)
               else ();
               (let uu____18528 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18528 with
                | (hd1,args) ->
                    let uu____18567 =
                      let uu____18568 = FStar_Syntax_Subst.compress hd1  in
                      uu____18568.FStar_Syntax_Syntax.n  in
                    (match uu____18567 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____18576 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18578 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18580 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18576 uu____18578 uu____18580)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18585 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18603 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18605 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18603
                    uu____18605)
               else ();
               (let uu____18610 = FStar_Syntax_Util.is_squash t  in
                match uu____18610 with
                | FStar_Pervasives_Native.Some (uu____18621,t') ->
                    is_applied bs t'
                | uu____18633 ->
                    let uu____18642 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18642 with
                     | FStar_Pervasives_Native.Some (uu____18653,t') ->
                         is_applied bs t'
                     | uu____18665 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18689 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18689 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18696)::(q,uu____18698)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18741 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18743 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18741 uu____18743)
                    else ();
                    (let uu____18748 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18748 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18753 =
                           let uu____18754 = FStar_Syntax_Subst.compress p
                              in
                           uu____18754.FStar_Syntax_Syntax.n  in
                         (match uu____18753 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18765 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18765))
                          | uu____18768 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18771)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18796 =
                           let uu____18797 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18797.FStar_Syntax_Syntax.n  in
                         (match uu____18796 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18808 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18808))
                          | uu____18811 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18815 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18815 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18820 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18820 with
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
                                     let uu____18834 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18834))
                               | uu____18837 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18842)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18867 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18867 with
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
                                     let uu____18881 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18881))
                               | uu____18884 -> FStar_Pervasives_Native.None)
                          | uu____18887 -> FStar_Pervasives_Native.None)
                     | uu____18890 -> FStar_Pervasives_Native.None))
               | uu____18893 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18906 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18906 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18912)::[],uu____18913,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18933 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18935 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18933
                         uu____18935)
                    else ();
                    is_quantified_const bv phi')
               | uu____18940 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18955 =
                 let uu____18956 = FStar_Syntax_Subst.compress phi  in
                 uu____18956.FStar_Syntax_Syntax.n  in
               match uu____18955 with
               | FStar_Syntax_Syntax.Tm_match (uu____18962,br::brs) ->
                   let uu____19029 = br  in
                   (match uu____19029 with
                    | (uu____19047,uu____19048,e) ->
                        let r =
                          let uu____19070 = simp_t e  in
                          match uu____19070 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____19082 =
                                FStar_List.for_all
                                  (fun uu____19101  ->
                                     match uu____19101 with
                                     | (uu____19115,uu____19116,e') ->
                                         let uu____19130 = simp_t e'  in
                                         uu____19130 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____19082
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____19146 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____19156 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____19156
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____19194 =
                 match uu____19194 with
                 | (t1,q) ->
                     let uu____19215 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____19215 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____19247 -> (t1, q))
                  in
               let uu____19260 = FStar_Syntax_Util.head_and_args t  in
               match uu____19260 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____19340 =
                 let uu____19341 = FStar_Syntax_Util.unmeta ty  in
                 uu____19341.FStar_Syntax_Syntax.n  in
               match uu____19340 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____19346) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____19351,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____19375 -> false  in
             let simplify1 arg =
               let uu____19408 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____19408, arg)  in
             let uu____19423 = is_forall_const tm1  in
             match uu____19423 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____19429 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____19431 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____19429
                       uu____19431)
                  else ();
                  (let uu____19436 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____19436))
             | FStar_Pervasives_Native.None  ->
                 let uu____19437 =
                   let uu____19438 = FStar_Syntax_Subst.compress tm1  in
                   uu____19438.FStar_Syntax_Syntax.n  in
                 (match uu____19437 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19442;
                              FStar_Syntax_Syntax.vars = uu____19443;_},uu____19444);
                         FStar_Syntax_Syntax.pos = uu____19445;
                         FStar_Syntax_Syntax.vars = uu____19446;_},args)
                      ->
                      let uu____19476 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19476
                      then
                        let uu____19479 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19479 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19537)::
                             (uu____19538,(arg,uu____19540))::[] ->
                             maybe_auto_squash arg
                         | (uu____19613,(arg,uu____19615))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19616)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19689)::uu____19690::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19760::(FStar_Pervasives_Native.Some (false
                                         ),uu____19761)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19831 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19849 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19849
                         then
                           let uu____19852 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19852 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19910)::uu____19911::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19981::(FStar_Pervasives_Native.Some (true
                                           ),uu____19982)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20052)::(uu____20053,(arg,uu____20055))::[]
                               -> maybe_auto_squash arg
                           | (uu____20128,(arg,uu____20130))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20131)::[]
                               -> maybe_auto_squash arg
                           | uu____20204 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20222 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20222
                            then
                              let uu____20225 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20225 with
                              | uu____20283::(FStar_Pervasives_Native.Some
                                              (true ),uu____20284)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20354)::uu____20355::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20425)::(uu____20426,(arg,uu____20428))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20501,(p,uu____20503))::(uu____20504,
                                                                (q,uu____20506))::[]
                                  ->
                                  let uu____20578 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20578
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20583 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20601 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20601
                               then
                                 let uu____20604 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20604 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20662)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20663)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20737)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20738)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20812)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20813)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20887)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20888)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20962,(arg,uu____20964))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20965)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21038)::(uu____21039,(arg,uu____21041))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21114,(arg,uu____21116))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21117)::[]
                                     ->
                                     let uu____21190 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21190
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21191)::(uu____21192,(arg,uu____21194))::[]
                                     ->
                                     let uu____21267 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21267
                                 | (uu____21268,(p,uu____21270))::(uu____21271,
                                                                   (q,uu____21273))::[]
                                     ->
                                     let uu____21345 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21345
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21350 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21368 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21368
                                  then
                                    let uu____21371 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21371 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21429)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21473)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21517 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21535 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21535
                                     then
                                       match args with
                                       | (t,uu____21539)::[] ->
                                           let uu____21564 =
                                             let uu____21565 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21565.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21564 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21568::[],body,uu____21570)
                                                ->
                                                let uu____21605 = simp_t body
                                                   in
                                                (match uu____21605 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21611 -> tm1)
                                            | uu____21615 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21617))::(t,uu____21619)::[]
                                           ->
                                           let uu____21659 =
                                             let uu____21660 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21660.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21659 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21663::[],body,uu____21665)
                                                ->
                                                let uu____21700 = simp_t body
                                                   in
                                                (match uu____21700 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21708 -> tm1)
                                            | uu____21712 -> tm1)
                                       | uu____21713 -> tm1
                                     else
                                       (let uu____21726 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21726
                                        then
                                          match args with
                                          | (t,uu____21730)::[] ->
                                              let uu____21755 =
                                                let uu____21756 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21756.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21755 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21759::[],body,uu____21761)
                                                   ->
                                                   let uu____21796 =
                                                     simp_t body  in
                                                   (match uu____21796 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21802 -> tm1)
                                               | uu____21806 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21808))::(t,uu____21810)::[]
                                              ->
                                              let uu____21850 =
                                                let uu____21851 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21851.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21850 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21854::[],body,uu____21856)
                                                   ->
                                                   let uu____21891 =
                                                     simp_t body  in
                                                   (match uu____21891 with
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
                                                    | uu____21899 -> tm1)
                                               | uu____21903 -> tm1)
                                          | uu____21904 -> tm1
                                        else
                                          (let uu____21917 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21917
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21920;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21921;_},uu____21922)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21948;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21949;_},uu____21950)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21976 -> tm1
                                           else
                                             (let uu____21989 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____21989
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____22003 =
                                                    let uu____22004 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____22004.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____22003 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____22015 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____22029 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____22029
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____22068 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____22068
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____22074 =
                                                         let uu____22075 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____22075.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____22074 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____22078 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____22086 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____22086
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____22095
                                                                  =
                                                                  let uu____22096
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____22096.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____22095
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____22102)
                                                                    -> hd1
                                                                | uu____22127
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____22131
                                                                =
                                                                let uu____22142
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____22142]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____22131)
                                                       | uu____22175 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____22180 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____22180 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____22200 ->
                                                     let uu____22209 =
                                                       let uu____22216 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____22216 cfg env
                                                        in
                                                     uu____22209 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____22222;
                         FStar_Syntax_Syntax.vars = uu____22223;_},args)
                      ->
                      let uu____22249 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22249
                      then
                        let uu____22252 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22252 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22310)::
                             (uu____22311,(arg,uu____22313))::[] ->
                             maybe_auto_squash arg
                         | (uu____22386,(arg,uu____22388))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22389)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22462)::uu____22463::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22533::(FStar_Pervasives_Native.Some (false
                                         ),uu____22534)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22604 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22622 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22622
                         then
                           let uu____22625 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22625 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22683)::uu____22684::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22754::(FStar_Pervasives_Native.Some (true
                                           ),uu____22755)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22825)::(uu____22826,(arg,uu____22828))::[]
                               -> maybe_auto_squash arg
                           | (uu____22901,(arg,uu____22903))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22904)::[]
                               -> maybe_auto_squash arg
                           | uu____22977 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22995 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22995
                            then
                              let uu____22998 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____22998 with
                              | uu____23056::(FStar_Pervasives_Native.Some
                                              (true ),uu____23057)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____23127)::uu____23128::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____23198)::(uu____23199,(arg,uu____23201))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23274,(p,uu____23276))::(uu____23277,
                                                                (q,uu____23279))::[]
                                  ->
                                  let uu____23351 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23351
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23356 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23374 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23374
                               then
                                 let uu____23377 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23377 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23435)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23436)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23510)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23511)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23585)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23586)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23660)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23661)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23735,(arg,uu____23737))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23738)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23811)::(uu____23812,(arg,uu____23814))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23887,(arg,uu____23889))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23890)::[]
                                     ->
                                     let uu____23963 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23963
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23964)::(uu____23965,(arg,uu____23967))::[]
                                     ->
                                     let uu____24040 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____24040
                                 | (uu____24041,(p,uu____24043))::(uu____24044,
                                                                   (q,uu____24046))::[]
                                     ->
                                     let uu____24118 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____24118
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____24123 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____24141 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____24141
                                  then
                                    let uu____24144 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____24144 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____24202)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____24246)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____24290 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____24308 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____24308
                                     then
                                       match args with
                                       | (t,uu____24312)::[] ->
                                           let uu____24337 =
                                             let uu____24338 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24338.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24337 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24341::[],body,uu____24343)
                                                ->
                                                let uu____24378 = simp_t body
                                                   in
                                                (match uu____24378 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24384 -> tm1)
                                            | uu____24388 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24390))::(t,uu____24392)::[]
                                           ->
                                           let uu____24432 =
                                             let uu____24433 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24433.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24432 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24436::[],body,uu____24438)
                                                ->
                                                let uu____24473 = simp_t body
                                                   in
                                                (match uu____24473 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24481 -> tm1)
                                            | uu____24485 -> tm1)
                                       | uu____24486 -> tm1
                                     else
                                       (let uu____24499 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24499
                                        then
                                          match args with
                                          | (t,uu____24503)::[] ->
                                              let uu____24528 =
                                                let uu____24529 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24529.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24528 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24532::[],body,uu____24534)
                                                   ->
                                                   let uu____24569 =
                                                     simp_t body  in
                                                   (match uu____24569 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24575 -> tm1)
                                               | uu____24579 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24581))::(t,uu____24583)::[]
                                              ->
                                              let uu____24623 =
                                                let uu____24624 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24624.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24623 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24627::[],body,uu____24629)
                                                   ->
                                                   let uu____24664 =
                                                     simp_t body  in
                                                   (match uu____24664 with
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
                                                    | uu____24672 -> tm1)
                                               | uu____24676 -> tm1)
                                          | uu____24677 -> tm1
                                        else
                                          (let uu____24690 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24690
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24693;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24694;_},uu____24695)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24721;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24722;_},uu____24723)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24749 -> tm1
                                           else
                                             (let uu____24762 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____24762
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____24776 =
                                                    let uu____24777 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____24777.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____24776 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____24788 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24802 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____24802
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____24837 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____24837
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24843 =
                                                         let uu____24844 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____24844.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____24843 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24847 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24855 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24855
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24864
                                                                  =
                                                                  let uu____24865
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24865.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24864
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____24871)
                                                                    -> hd1
                                                                | uu____24896
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____24900
                                                                =
                                                                let uu____24911
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____24911]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24900)
                                                       | uu____24944 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24949 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____24949 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24969 ->
                                                     let uu____24978 =
                                                       let uu____24985 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____24985 cfg env
                                                        in
                                                     uu____24978 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24996 = simp_t t  in
                      (match uu____24996 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____25005 ->
                      let uu____25028 = is_const_match tm1  in
                      (match uu____25028 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____25037 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____25047  ->
               (let uu____25049 = FStar_Syntax_Print.tag_of_term t  in
                let uu____25051 = FStar_Syntax_Print.term_to_string t  in
                let uu____25053 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____25061 =
                  let uu____25063 =
                    let uu____25066 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____25066
                     in
                  stack_to_string uu____25063  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____25049 uu____25051 uu____25053 uu____25061);
               (let uu____25091 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____25091
                then
                  let uu____25095 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____25095 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____25102 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____25104 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____25106 =
                          let uu____25108 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____25108
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____25102
                          uu____25104 uu____25106);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____25130 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____25138)::uu____25139 -> true
                | uu____25149 -> false)
              in
           if uu____25130
           then
             let uu____25152 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____25152 (norm cfg env stack)
           else
             (let t_opt = is_wp_req_ens_commutation cfg t  in
              let uu____25160 = FStar_All.pipe_right t_opt FStar_Util.is_some
                 in
              if uu____25160
              then
                ((let uu____25167 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         cfg.FStar_TypeChecker_Cfg.tcenv)
                      (FStar_Options.Other "WPReqEns")
                     in
                  if uu____25167
                  then
                    let uu____25172 = FStar_Syntax_Print.term_to_string t  in
                    let uu____25174 =
                      let uu____25176 =
                        FStar_All.pipe_right t_opt FStar_Util.must  in
                      FStar_All.pipe_right uu____25176
                        FStar_Syntax_Print.term_to_string
                       in
                    FStar_Util.print2
                      "In rebuild: reduced a wp req ens commutation from \n%s\n to \n%s"
                      uu____25172 uu____25174
                  else ());
                 (let uu____25183 =
                    FStar_All.pipe_right t_opt FStar_Util.must  in
                  FStar_All.pipe_right uu____25183 (norm cfg env stack)))
              else
                (let t1 = maybe_simplify cfg env stack t  in
                 match stack with
                 | [] -> t1
                 | (Debug (tm,time_then))::stack1 ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let time_now = FStar_Util.now ()  in
                         let uu____25197 =
                           let uu____25199 =
                             let uu____25201 =
                               FStar_Util.time_diff time_then time_now  in
                             FStar_Pervasives_Native.snd uu____25201  in
                           FStar_Util.string_of_int uu____25199  in
                         let uu____25208 =
                           FStar_Syntax_Print.term_to_string tm  in
                         let uu____25210 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                         let uu____25212 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print4
                           "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____25197 uu____25208 uu____25210 uu____25212)
                      else ();
                      rebuild cfg env stack1 t1)
                 | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
                 | (Meta (uu____25221,m,r))::stack1 ->
                     let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                     rebuild cfg env stack1 t2
                 | (MemoLazy r)::stack1 ->
                     (set_memo cfg r (env, t1);
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____25250  ->
                           let uu____25251 =
                             FStar_Syntax_Print.term_to_string t1  in
                           FStar_Util.print1 "\tSet memo %s\n" uu____25251);
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
                     let uu____25294 =
                       let uu___2948_25295 =
                         FStar_Syntax_Util.abs bs1 t1 lopt1  in
                       {
                         FStar_Syntax_Syntax.n =
                           (uu___2948_25295.FStar_Syntax_Syntax.n);
                         FStar_Syntax_Syntax.pos = r;
                         FStar_Syntax_Syntax.vars =
                           (uu___2948_25295.FStar_Syntax_Syntax.vars)
                       }  in
                     rebuild cfg env stack1 uu____25294
                 | (Arg
                     (Univ uu____25298,uu____25299,uu____25300))::uu____25301
                     -> failwith "Impossible"
                 | (Arg (Dummy ,uu____25305,uu____25306))::uu____25307 ->
                     failwith "Impossible"
                 | (UnivArgs (us,r))::stack1 ->
                     let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                     rebuild cfg env stack1 t2
                 | (Arg
                     (Clos (env_arg,tm,uu____25323,uu____25324),aq,r))::stack1
                     when
                     let uu____25376 = head_of t1  in
                     FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____25376
                     ->
                     let t2 =
                       let uu____25380 =
                         let uu____25385 =
                           let uu____25386 = closure_as_term cfg env_arg tm
                              in
                           (uu____25386, aq)  in
                         FStar_Syntax_Syntax.extend_app t1 uu____25385  in
                       uu____25380 FStar_Pervasives_Native.None r  in
                     rebuild cfg env stack1 t2
                 | (Arg (Clos (env_arg,tm,m,uu____25396),aq,r))::stack1 ->
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____25451  ->
                           let uu____25452 =
                             FStar_Syntax_Print.term_to_string tm  in
                           FStar_Util.print1 "Rebuilding with arg %s\n"
                             uu____25452);
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
                        (let uu____25472 = FStar_ST.op_Bang m  in
                         match uu____25472 with
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
                         | FStar_Pervasives_Native.Some (uu____25560,a) ->
                             let t2 =
                               FStar_Syntax_Syntax.extend_app t1 (a, aq)
                                 FStar_Pervasives_Native.None r
                                in
                             rebuild cfg env_arg stack1 t2))
                 | (App (env1,head1,aq,r))::stack' when
                     should_reify cfg stack ->
                     let t0 = t1  in
                     let fallback msg uu____25616 =
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____25621  ->
                            let uu____25622 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not reifying%s: %s\n" msg
                              uu____25622);
                       (let t2 =
                          FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                            FStar_Pervasives_Native.None r
                           in
                        rebuild cfg env1 stack' t2)
                        in
                     let uu____25632 =
                       let uu____25633 = FStar_Syntax_Subst.compress t1  in
                       uu____25633.FStar_Syntax_Syntax.n  in
                     (match uu____25632 with
                      | FStar_Syntax_Syntax.Tm_meta
                          (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                          do_reify_monadic (fallback " (1)") cfg env1 stack
                            t2 m ty
                      | FStar_Syntax_Syntax.Tm_meta
                          (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                           (msrc,mtgt,ty))
                          ->
                          let lifted =
                            let uu____25661 = closure_as_term cfg env1 ty  in
                            reify_lift cfg t2 msrc mtgt uu____25661  in
                          (FStar_TypeChecker_Cfg.log cfg
                             (fun uu____25665  ->
                                let uu____25666 =
                                  FStar_Syntax_Print.term_to_string lifted
                                   in
                                FStar_Util.print1 "Reified lift to (1): %s\n"
                                  uu____25666);
                           (let uu____25669 = FStar_List.tl stack  in
                            norm cfg env1 uu____25669 lifted))
                      | FStar_Syntax_Syntax.Tm_app
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reflect uu____25670);
                             FStar_Syntax_Syntax.pos = uu____25671;
                             FStar_Syntax_Syntax.vars = uu____25672;_},
                           (e,uu____25674)::[])
                          -> norm cfg env1 stack' e
                      | FStar_Syntax_Syntax.Tm_app uu____25713 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                          ->
                          let uu____25730 =
                            FStar_Syntax_Util.head_and_args t1  in
                          (match uu____25730 with
                           | (hd1,args) ->
                               let uu____25773 =
                                 let uu____25774 =
                                   FStar_Syntax_Util.un_uinst hd1  in
                                 uu____25774.FStar_Syntax_Syntax.n  in
                               (match uu____25773 with
                                | FStar_Syntax_Syntax.Tm_fvar fv ->
                                    let uu____25778 =
                                      FStar_TypeChecker_Cfg.find_prim_step
                                        cfg fv
                                       in
                                    (match uu____25778 with
                                     | FStar_Pervasives_Native.Some
                                         {
                                           FStar_TypeChecker_Cfg.name =
                                             uu____25781;
                                           FStar_TypeChecker_Cfg.arity =
                                             uu____25782;
                                           FStar_TypeChecker_Cfg.univ_arity =
                                             uu____25783;
                                           FStar_TypeChecker_Cfg.auto_reflect
                                             = FStar_Pervasives_Native.Some
                                             n1;
                                           FStar_TypeChecker_Cfg.strong_reduction_ok
                                             = uu____25785;
                                           FStar_TypeChecker_Cfg.requires_binder_substitution
                                             = uu____25786;
                                           FStar_TypeChecker_Cfg.interpretation
                                             = uu____25787;
                                           FStar_TypeChecker_Cfg.interpretation_nbe
                                             = uu____25788;_}
                                         when (FStar_List.length args) = n1
                                         -> norm cfg env1 stack' t1
                                     | uu____25824 -> fallback " (3)" ())
                                | uu____25828 -> fallback " (4)" ()))
                      | uu____25830 -> fallback " (2)" ())
                 | (App (env1,head1,aq,r))::stack1 ->
                     let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack1 t2
                 | (Match (env',branches,cfg1,r))::stack1 ->
                     (FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25856  ->
                           let uu____25857 =
                             FStar_Syntax_Print.term_to_string t1  in
                           FStar_Util.print1
                             "Rebuilding with match, scrutinee is %s ...\n"
                             uu____25857);
                      (let scrutinee_env = env  in
                       let env1 = env'  in
                       let scrutinee = t1  in
                       let norm_and_rebuild_match uu____25868 =
                         FStar_TypeChecker_Cfg.log cfg1
                           (fun uu____25873  ->
                              let uu____25874 =
                                FStar_Syntax_Print.term_to_string scrutinee
                                 in
                              let uu____25876 =
                                let uu____25878 =
                                  FStar_All.pipe_right branches
                                    (FStar_List.map
                                       (fun uu____25908  ->
                                          match uu____25908 with
                                          | (p,uu____25919,uu____25920) ->
                                              FStar_Syntax_Print.pat_to_string
                                                p))
                                   in
                                FStar_All.pipe_right uu____25878
                                  (FStar_String.concat "\n\t")
                                 in
                              FStar_Util.print2
                                "match is irreducible: scrutinee=%s\nbranches=%s\n"
                                uu____25874 uu____25876);
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
                                   (fun uu___16_25942  ->
                                      match uu___16_25942 with
                                      | FStar_TypeChecker_Env.InliningDelta 
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                           -> true
                                      | uu____25946 -> false))
                               in
                            let steps =
                              let uu___3116_25949 =
                                cfg1.FStar_TypeChecker_Cfg.steps  in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3116_25949.FStar_TypeChecker_Cfg.for_extraction)
                              }  in
                            let uu___3119_25956 = cfg1  in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3119_25956.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3119_25956.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3119_25956.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3119_25956.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3119_25956.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3119_25956.FStar_TypeChecker_Cfg.reifying)
                            }  in
                          let norm_or_whnf env2 t2 =
                            if whnf
                            then closure_as_term cfg_exclude_zeta env2 t2
                            else norm cfg_exclude_zeta env2 [] t2  in
                          let rec norm_pat env2 p =
                            match p.FStar_Syntax_Syntax.v with
                            | FStar_Syntax_Syntax.Pat_constant uu____26031 ->
                                (p, env2)
                            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                                let uu____26062 =
                                  FStar_All.pipe_right pats
                                    (FStar_List.fold_left
                                       (fun uu____26151  ->
                                          fun uu____26152  ->
                                            match (uu____26151, uu____26152)
                                            with
                                            | ((pats1,env3),(p1,b)) ->
                                                let uu____26302 =
                                                  norm_pat env3 p1  in
                                                (match uu____26302 with
                                                 | (p2,env4) ->
                                                     (((p2, b) :: pats1),
                                                       env4))) ([], env2))
                                   in
                                (match uu____26062 with
                                 | (pats1,env3) ->
                                     ((let uu___3147_26472 = p  in
                                       {
                                         FStar_Syntax_Syntax.v =
                                           (FStar_Syntax_Syntax.Pat_cons
                                              (fv, (FStar_List.rev pats1)));
                                         FStar_Syntax_Syntax.p =
                                           (uu___3147_26472.FStar_Syntax_Syntax.p)
                                       }), env3))
                            | FStar_Syntax_Syntax.Pat_var x ->
                                let x1 =
                                  let uu___3151_26493 = x  in
                                  let uu____26494 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3151_26493.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3151_26493.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26494
                                  }  in
                                ((let uu___3154_26508 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_var x1);
                                    FStar_Syntax_Syntax.p =
                                      (uu___3154_26508.FStar_Syntax_Syntax.p)
                                  }), (dummy :: env2))
                            | FStar_Syntax_Syntax.Pat_wild x ->
                                let x1 =
                                  let uu___3158_26519 = x  in
                                  let uu____26520 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3158_26519.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3158_26519.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26520
                                  }  in
                                ((let uu___3161_26534 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_wild x1);
                                    FStar_Syntax_Syntax.p =
                                      (uu___3161_26534.FStar_Syntax_Syntax.p)
                                  }), (dummy :: env2))
                            | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                                let x1 =
                                  let uu___3167_26550 = x  in
                                  let uu____26551 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3167_26550.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3167_26550.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26551
                                  }  in
                                let t3 = norm_or_whnf env2 t2  in
                                ((let uu___3171_26566 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_dot_term
                                         (x1, t3));
                                    FStar_Syntax_Syntax.p =
                                      (uu___3171_26566.FStar_Syntax_Syntax.p)
                                  }), env2)
                             in
                          let branches1 =
                            match env1 with
                            | [] when whnf -> branches
                            | uu____26610 ->
                                FStar_All.pipe_right branches
                                  (FStar_List.map
                                     (fun branch1  ->
                                        let uu____26640 =
                                          FStar_Syntax_Subst.open_branch
                                            branch1
                                           in
                                        match uu____26640 with
                                        | (p,wopt,e) ->
                                            let uu____26660 = norm_pat env1 p
                                               in
                                            (match uu____26660 with
                                             | (p1,env2) ->
                                                 let wopt1 =
                                                   match wopt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       FStar_Pervasives_Native.None
                                                   | FStar_Pervasives_Native.Some
                                                       w ->
                                                       let uu____26715 =
                                                         norm_or_whnf env2 w
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____26715
                                                    in
                                                 let e1 = norm_or_whnf env2 e
                                                    in
                                                 FStar_Syntax_Util.branch
                                                   (p1, wopt1, e1))))
                             in
                          let scrutinee1 =
                            let uu____26732 =
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
                            if uu____26732
                            then
                              norm
                                (let uu___3190_26739 = cfg1  in
                                 {
                                   FStar_TypeChecker_Cfg.steps =
                                     (let uu___3192_26742 =
                                        cfg1.FStar_TypeChecker_Cfg.steps  in
                                      {
                                        FStar_TypeChecker_Cfg.beta =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.beta);
                                        FStar_TypeChecker_Cfg.iota =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.iota);
                                        FStar_TypeChecker_Cfg.zeta =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.zeta);
                                        FStar_TypeChecker_Cfg.weak =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.weak);
                                        FStar_TypeChecker_Cfg.hnf =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.hnf);
                                        FStar_TypeChecker_Cfg.primops =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.primops);
                                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                          =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                        FStar_TypeChecker_Cfg.unfold_until =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.unfold_until);
                                        FStar_TypeChecker_Cfg.unfold_only =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.unfold_only);
                                        FStar_TypeChecker_Cfg.unfold_fully =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.unfold_fully);
                                        FStar_TypeChecker_Cfg.unfold_attr =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.unfold_attr);
                                        FStar_TypeChecker_Cfg.unfold_tac =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.unfold_tac);
                                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                          =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                        FStar_TypeChecker_Cfg.simplify =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.simplify);
                                        FStar_TypeChecker_Cfg.erase_universes
                                          =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.erase_universes);
                                        FStar_TypeChecker_Cfg.allow_unbound_universes
                                          =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                        FStar_TypeChecker_Cfg.reify_ =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.reify_);
                                        FStar_TypeChecker_Cfg.compress_uvars
                                          =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.compress_uvars);
                                        FStar_TypeChecker_Cfg.no_full_norm =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.no_full_norm);
                                        FStar_TypeChecker_Cfg.check_no_uvars
                                          =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.check_no_uvars);
                                        FStar_TypeChecker_Cfg.unmeta =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.unmeta);
                                        FStar_TypeChecker_Cfg.unascribe =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.unascribe);
                                        FStar_TypeChecker_Cfg.in_full_norm_request
                                          =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.in_full_norm_request);
                                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                          = false;
                                        FStar_TypeChecker_Cfg.nbe_step =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.nbe_step);
                                        FStar_TypeChecker_Cfg.for_extraction
                                          =
                                          (uu___3192_26742.FStar_TypeChecker_Cfg.for_extraction)
                                      });
                                   FStar_TypeChecker_Cfg.tcenv =
                                     (uu___3190_26739.FStar_TypeChecker_Cfg.tcenv);
                                   FStar_TypeChecker_Cfg.debug =
                                     (uu___3190_26739.FStar_TypeChecker_Cfg.debug);
                                   FStar_TypeChecker_Cfg.delta_level =
                                     (uu___3190_26739.FStar_TypeChecker_Cfg.delta_level);
                                   FStar_TypeChecker_Cfg.primitive_steps =
                                     (uu___3190_26739.FStar_TypeChecker_Cfg.primitive_steps);
                                   FStar_TypeChecker_Cfg.strong =
                                     (uu___3190_26739.FStar_TypeChecker_Cfg.strong);
                                   FStar_TypeChecker_Cfg.memoize_lazy =
                                     (uu___3190_26739.FStar_TypeChecker_Cfg.memoize_lazy);
                                   FStar_TypeChecker_Cfg.normalize_pure_lets
                                     =
                                     (uu___3190_26739.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                   FStar_TypeChecker_Cfg.reifying =
                                     (uu___3190_26739.FStar_TypeChecker_Cfg.reifying)
                                 }) scrutinee_env [] scrutinee
                            else scrutinee  in
                          let uu____26746 =
                            mk
                              (FStar_Syntax_Syntax.Tm_match
                                 (scrutinee1, branches1)) r
                             in
                          rebuild cfg1 env1 stack1 uu____26746)
                          in
                       let rec is_cons head1 =
                         let uu____26772 =
                           let uu____26773 =
                             FStar_Syntax_Subst.compress head1  in
                           uu____26773.FStar_Syntax_Syntax.n  in
                         match uu____26772 with
                         | FStar_Syntax_Syntax.Tm_uinst (h,uu____26778) ->
                             is_cons h
                         | FStar_Syntax_Syntax.Tm_constant uu____26783 ->
                             true
                         | FStar_Syntax_Syntax.Tm_fvar
                             { FStar_Syntax_Syntax.fv_name = uu____26785;
                               FStar_Syntax_Syntax.fv_delta = uu____26786;
                               FStar_Syntax_Syntax.fv_qual =
                                 FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Data_ctor );_}
                             -> true
                         | FStar_Syntax_Syntax.Tm_fvar
                             { FStar_Syntax_Syntax.fv_name = uu____26788;
                               FStar_Syntax_Syntax.fv_delta = uu____26789;
                               FStar_Syntax_Syntax.fv_qual =
                                 FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Record_ctor
                                 uu____26790);_}
                             -> true
                         | uu____26798 -> false  in
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
                         let uu____26967 =
                           FStar_Syntax_Util.head_and_args scrutinee2  in
                         match uu____26967 with
                         | (head1,args) ->
                             (match p.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_var bv ->
                                  FStar_Util.Inl [(bv, scrutinee_orig)]
                              | FStar_Syntax_Syntax.Pat_wild bv ->
                                  FStar_Util.Inl [(bv, scrutinee_orig)]
                              | FStar_Syntax_Syntax.Pat_dot_term uu____27064
                                  -> FStar_Util.Inl []
                              | FStar_Syntax_Syntax.Pat_constant s ->
                                  (match scrutinee2.FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_constant s' when
                                       FStar_Const.eq_const s s' ->
                                       FStar_Util.Inl []
                                   | uu____27106 ->
                                       let uu____27107 =
                                         let uu____27109 = is_cons head1  in
                                         Prims.op_Negation uu____27109  in
                                       FStar_Util.Inr uu____27107)
                              | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                                  let uu____27138 =
                                    let uu____27139 =
                                      FStar_Syntax_Util.un_uinst head1  in
                                    uu____27139.FStar_Syntax_Syntax.n  in
                                  (match uu____27138 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv' when
                                       FStar_Syntax_Syntax.fv_eq fv fv' ->
                                       matches_args [] args arg_pats
                                   | uu____27158 ->
                                       let uu____27159 =
                                         let uu____27161 = is_cons head1  in
                                         Prims.op_Negation uu____27161  in
                                       FStar_Util.Inr uu____27159))
                       
                       and matches_args out a p =
                         match (a, p) with
                         | ([],[]) -> FStar_Util.Inl out
                         | ((t2,uu____27252)::rest_a,(p1,uu____27255)::rest_p)
                             ->
                             let uu____27314 = matches_pat t2 p1  in
                             (match uu____27314 with
                              | FStar_Util.Inl s ->
                                  matches_args (FStar_List.append out s)
                                    rest_a rest_p
                              | m -> m)
                         | uu____27367 -> FStar_Util.Inr false
                        in
                       let rec matches scrutinee1 p =
                         match p with
                         | [] -> norm_and_rebuild_match ()
                         | (p1,wopt,b)::rest ->
                             let uu____27490 = matches_pat scrutinee1 p1  in
                             (match uu____27490 with
                              | FStar_Util.Inr (false ) ->
                                  matches scrutinee1 rest
                              | FStar_Util.Inr (true ) ->
                                  norm_and_rebuild_match ()
                              | FStar_Util.Inl s ->
                                  (FStar_TypeChecker_Cfg.log cfg1
                                     (fun uu____27536  ->
                                        let uu____27537 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        let uu____27539 =
                                          let uu____27541 =
                                            FStar_List.map
                                              (fun uu____27553  ->
                                                 match uu____27553 with
                                                 | (uu____27559,t2) ->
                                                     FStar_Syntax_Print.term_to_string
                                                       t2) s
                                             in
                                          FStar_All.pipe_right uu____27541
                                            (FStar_String.concat "; ")
                                           in
                                        FStar_Util.print2
                                          "Matches pattern %s with subst = %s\n"
                                          uu____27537 uu____27539);
                                   (let env0 = env1  in
                                    let env2 =
                                      FStar_List.fold_left
                                        (fun env2  ->
                                           fun uu____27595  ->
                                             match uu____27595 with
                                             | (bv,t2) ->
                                                 let uu____27618 =
                                                   let uu____27625 =
                                                     let uu____27628 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         bv
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____27628
                                                      in
                                                   let uu____27629 =
                                                     let uu____27630 =
                                                       let uu____27662 =
                                                         FStar_Util.mk_ref
                                                           (FStar_Pervasives_Native.Some
                                                              ([], t2))
                                                          in
                                                       ([], t2, uu____27662,
                                                         false)
                                                        in
                                                     Clos uu____27630  in
                                                   (uu____27625, uu____27629)
                                                    in
                                                 uu____27618 :: env2) env1 s
                                       in
                                    let uu____27755 =
                                      guard_when_clause wopt b rest  in
                                    norm cfg1 env2 stack1 uu____27755)))
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
            (fun uu____27788  ->
               let uu____27789 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____27789);
          (let uu____27792 = is_nbe_request s  in
           if uu____27792
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27798  ->
                   let uu____27799 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27799);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27805  ->
                   let uu____27806 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27806);
              (let uu____27809 =
                 FStar_Util.record_time (fun uu____27816  -> nbe_eval c s t)
                  in
               match uu____27809 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27825  ->
                         let uu____27826 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27828 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27826 uu____27828);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27836  ->
                   let uu____27837 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27837);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27843  ->
                   let uu____27844 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27844);
              (let uu____27847 =
                 FStar_Util.record_time (fun uu____27854  -> norm c [] [] t)
                  in
               match uu____27847 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27869  ->
                         let uu____27870 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27872 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27870 uu____27872);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27891 =
          let uu____27895 =
            let uu____27897 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____27897  in
          FStar_Pervasives_Native.Some uu____27895  in
        FStar_Profiling.profile
          (fun uu____27900  -> normalize_with_primitive_steps [] s e t)
          uu____27891 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____27922  ->
             let uu____27923 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27923);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27929  ->
             let uu____27930 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27930);
        (let uu____27933 =
           FStar_Util.record_time (fun uu____27940  -> norm_comp cfg [] c)
            in
         match uu____27933 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27955  ->
                   let uu____27956 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____27958 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27956
                     uu____27958);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27972 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____27972 [] u
  
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
      let uu____27994 = normalize steps env t  in
      FStar_TypeChecker_Env.non_informative env uu____27994
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____28006 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env t ->
          let uu___3360_28025 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3360_28025.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3360_28025.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____28032 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____28032
          then
            let ct1 =
              let uu____28036 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____28036 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____28043 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____28043
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3370_28050 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3370_28050.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3370_28050.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3370_28050.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c
                     in
                  let uu___3374_28052 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3374_28052.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3374_28052.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3374_28052.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3374_28052.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3377_28053 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3377_28053.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3377_28053.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____28056 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      let uu____28068 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____28068
      then
        let uu____28071 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____28071 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3385_28075 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3385_28075.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3385_28075.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3385_28075.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3392_28094  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3391_28097 ->
            ((let uu____28099 =
                let uu____28105 =
                  let uu____28107 = FStar_Util.message_of_exn uu___3391_28097
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____28107
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____28105)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____28099);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3402_28126  ->
             match () with
             | () ->
                 let uu____28127 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____28127 [] c) ()
        with
        | uu___3401_28136 ->
            ((let uu____28138 =
                let uu____28144 =
                  let uu____28146 = FStar_Util.message_of_exn uu___3401_28136
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____28146
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____28144)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____28138);
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
                   let uu____28195 =
                     let uu____28196 =
                       let uu____28203 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____28203)  in
                     FStar_Syntax_Syntax.Tm_refine uu____28196  in
                   mk uu____28195 t01.FStar_Syntax_Syntax.pos
               | uu____28208 -> t2)
          | uu____28209 -> t2  in
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
        let uu____28303 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____28303 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____28340 ->
                 let uu____28349 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____28349 with
                  | (actuals,uu____28359,uu____28360) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____28380 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____28380 with
                         | (binders,args) ->
                             let uu____28391 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____28391
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
      | uu____28406 ->
          let uu____28407 = FStar_Syntax_Util.head_and_args t  in
          (match uu____28407 with
           | (head1,args) ->
               let uu____28450 =
                 let uu____28451 = FStar_Syntax_Subst.compress head1  in
                 uu____28451.FStar_Syntax_Syntax.n  in
               (match uu____28450 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____28472 =
                      let uu____28487 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____28487  in
                    (match uu____28472 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____28527 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3472_28535 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3472_28535.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3472_28535.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3472_28535.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3472_28535.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3472_28535.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3472_28535.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3472_28535.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3472_28535.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3472_28535.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3472_28535.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3472_28535.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3472_28535.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3472_28535.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3472_28535.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3472_28535.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3472_28535.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3472_28535.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3472_28535.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3472_28535.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3472_28535.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3472_28535.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3472_28535.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3472_28535.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3472_28535.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3472_28535.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3472_28535.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3472_28535.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3472_28535.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3472_28535.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3472_28535.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3472_28535.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3472_28535.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3472_28535.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3472_28535.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3472_28535.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3472_28535.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3472_28535.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3472_28535.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3472_28535.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3472_28535.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3472_28535.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3472_28535.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3472_28535.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____28527 with
                            | (uu____28538,ty,uu____28540) ->
                                eta_expand_with_type env t ty))
                | uu____28541 ->
                    let uu____28542 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3479_28550 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3479_28550.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3479_28550.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3479_28550.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3479_28550.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3479_28550.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3479_28550.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3479_28550.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3479_28550.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3479_28550.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3479_28550.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3479_28550.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3479_28550.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3479_28550.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3479_28550.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3479_28550.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3479_28550.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3479_28550.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3479_28550.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3479_28550.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3479_28550.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3479_28550.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3479_28550.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3479_28550.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3479_28550.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3479_28550.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3479_28550.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3479_28550.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3479_28550.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3479_28550.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3479_28550.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3479_28550.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3479_28550.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3479_28550.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3479_28550.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3479_28550.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3479_28550.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3479_28550.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3479_28550.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3479_28550.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3479_28550.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3479_28550.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3479_28550.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3479_28550.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____28542 with
                     | (uu____28553,ty,uu____28555) ->
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
      let uu___3491_28637 = x  in
      let uu____28638 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3491_28637.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3491_28637.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28638
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28641 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28665 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28666 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28667 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28668 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28675 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28676 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28677 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3517_28711 = rc  in
          let uu____28712 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28721 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3517_28711.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28712;
            FStar_Syntax_Syntax.residual_flags = uu____28721
          }  in
        let uu____28724 =
          let uu____28725 =
            let uu____28744 = elim_delayed_subst_binders bs  in
            let uu____28753 = elim_delayed_subst_term t2  in
            let uu____28756 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28744, uu____28753, uu____28756)  in
          FStar_Syntax_Syntax.Tm_abs uu____28725  in
        mk1 uu____28724
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28793 =
          let uu____28794 =
            let uu____28809 = elim_delayed_subst_binders bs  in
            let uu____28818 = elim_delayed_subst_comp c  in
            (uu____28809, uu____28818)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28794  in
        mk1 uu____28793
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28837 =
          let uu____28838 =
            let uu____28845 = elim_bv bv  in
            let uu____28846 = elim_delayed_subst_term phi  in
            (uu____28845, uu____28846)  in
          FStar_Syntax_Syntax.Tm_refine uu____28838  in
        mk1 uu____28837
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28877 =
          let uu____28878 =
            let uu____28895 = elim_delayed_subst_term t2  in
            let uu____28898 = elim_delayed_subst_args args  in
            (uu____28895, uu____28898)  in
          FStar_Syntax_Syntax.Tm_app uu____28878  in
        mk1 uu____28877
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3539_28970 = p  in
              let uu____28971 =
                let uu____28972 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28972  in
              {
                FStar_Syntax_Syntax.v = uu____28971;
                FStar_Syntax_Syntax.p =
                  (uu___3539_28970.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3543_28974 = p  in
              let uu____28975 =
                let uu____28976 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28976  in
              {
                FStar_Syntax_Syntax.v = uu____28975;
                FStar_Syntax_Syntax.p =
                  (uu___3543_28974.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3549_28983 = p  in
              let uu____28984 =
                let uu____28985 =
                  let uu____28992 = elim_bv x  in
                  let uu____28993 = elim_delayed_subst_term t0  in
                  (uu____28992, uu____28993)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28985  in
              {
                FStar_Syntax_Syntax.v = uu____28984;
                FStar_Syntax_Syntax.p =
                  (uu___3549_28983.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3555_29018 = p  in
              let uu____29019 =
                let uu____29020 =
                  let uu____29034 =
                    FStar_List.map
                      (fun uu____29060  ->
                         match uu____29060 with
                         | (x,b) ->
                             let uu____29077 = elim_pat x  in
                             (uu____29077, b)) pats
                     in
                  (fv, uu____29034)  in
                FStar_Syntax_Syntax.Pat_cons uu____29020  in
              {
                FStar_Syntax_Syntax.v = uu____29019;
                FStar_Syntax_Syntax.p =
                  (uu___3555_29018.FStar_Syntax_Syntax.p)
              }
          | uu____29092 -> p  in
        let elim_branch uu____29116 =
          match uu____29116 with
          | (pat,wopt,t3) ->
              let uu____29142 = elim_pat pat  in
              let uu____29145 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____29148 = elim_delayed_subst_term t3  in
              (uu____29142, uu____29145, uu____29148)
           in
        let uu____29153 =
          let uu____29154 =
            let uu____29177 = elim_delayed_subst_term t2  in
            let uu____29180 = FStar_List.map elim_branch branches  in
            (uu____29177, uu____29180)  in
          FStar_Syntax_Syntax.Tm_match uu____29154  in
        mk1 uu____29153
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____29311 =
          match uu____29311 with
          | (tc,topt) ->
              let uu____29346 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____29356 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____29356
                | FStar_Util.Inr c ->
                    let uu____29358 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____29358
                 in
              let uu____29359 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____29346, uu____29359)
           in
        let uu____29368 =
          let uu____29369 =
            let uu____29396 = elim_delayed_subst_term t2  in
            let uu____29399 = elim_ascription a  in
            (uu____29396, uu____29399, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____29369  in
        mk1 uu____29368
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3585_29462 = lb  in
          let uu____29463 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____29466 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3585_29462.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3585_29462.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____29463;
            FStar_Syntax_Syntax.lbeff =
              (uu___3585_29462.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____29466;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3585_29462.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3585_29462.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____29469 =
          let uu____29470 =
            let uu____29484 =
              let uu____29492 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____29492)  in
            let uu____29504 = elim_delayed_subst_term t2  in
            (uu____29484, uu____29504)  in
          FStar_Syntax_Syntax.Tm_let uu____29470  in
        mk1 uu____29469
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____29549 =
          let uu____29550 =
            let uu____29557 = elim_delayed_subst_term tm  in
            (uu____29557, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____29550  in
        mk1 uu____29549
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29568 =
          let uu____29569 =
            let uu____29576 = elim_delayed_subst_term t2  in
            let uu____29579 = elim_delayed_subst_meta md  in
            (uu____29576, uu____29579)  in
          FStar_Syntax_Syntax.Tm_meta uu____29569  in
        mk1 uu____29568

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29588  ->
         match uu___17_29588 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29592 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29592
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
        let uu____29615 =
          let uu____29616 =
            let uu____29625 = elim_delayed_subst_term t  in
            (uu____29625, uopt)  in
          FStar_Syntax_Syntax.Total uu____29616  in
        mk1 uu____29615
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29642 =
          let uu____29643 =
            let uu____29652 = elim_delayed_subst_term t  in
            (uu____29652, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29643  in
        mk1 uu____29642
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3618_29661 = ct  in
          let uu____29662 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29665 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29676 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3618_29661.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3618_29661.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29662;
            FStar_Syntax_Syntax.effect_args = uu____29665;
            FStar_Syntax_Syntax.flags = uu____29676
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29679  ->
    match uu___18_29679 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____29714 =
          let uu____29735 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____29744 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29735, uu____29744)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29714
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____29799 =
          let uu____29806 = elim_delayed_subst_term t  in (m, uu____29806)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____29799
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____29818 =
          let uu____29827 = elim_delayed_subst_term t  in
          (m1, m2, uu____29827)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29818
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
      (fun uu____29860  ->
         match uu____29860 with
         | (t,q) ->
             let uu____29879 = elim_delayed_subst_term t  in (uu____29879, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29907  ->
         match uu____29907 with
         | (x,q) ->
             let uu____29926 =
               let uu___3644_29927 = x  in
               let uu____29928 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3644_29927.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3644_29927.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29928
               }  in
             (uu____29926, q)) bs

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
            | (uu____30036,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____30068,FStar_Util.Inl t) ->
                let uu____30090 =
                  let uu____30097 =
                    let uu____30098 =
                      let uu____30113 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____30113)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____30098  in
                  FStar_Syntax_Syntax.mk uu____30097  in
                uu____30090 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____30126 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____30126 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____30158 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____30231 ->
                    let uu____30232 =
                      let uu____30241 =
                        let uu____30242 = FStar_Syntax_Subst.compress t4  in
                        uu____30242.FStar_Syntax_Syntax.n  in
                      (uu____30241, tc)  in
                    (match uu____30232 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____30271) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____30318) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____30363,FStar_Util.Inl uu____30364) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____30395 -> failwith "Impossible")
                 in
              (match uu____30158 with
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
          let uu____30534 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____30534 with
          | (univ_names1,binders1,tc) ->
              let uu____30608 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30608)
  
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
          let uu____30662 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____30662 with
          | (univ_names1,binders1,tc) ->
              let uu____30736 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30736)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____30778 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____30778 with
           | (univ_names1,binders1,typ1) ->
               let uu___3727_30818 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3727_30818.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3727_30818.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3727_30818.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3727_30818.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3727_30818.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3733_30833 = s  in
          let uu____30834 =
            let uu____30835 =
              let uu____30844 = FStar_List.map (elim_uvars env) sigs  in
              (uu____30844, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____30835  in
          {
            FStar_Syntax_Syntax.sigel = uu____30834;
            FStar_Syntax_Syntax.sigrng =
              (uu___3733_30833.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3733_30833.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3733_30833.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3733_30833.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3733_30833.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____30863 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30863 with
           | (univ_names1,uu____30887,typ1) ->
               let uu___3747_30909 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3747_30909.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3747_30909.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3747_30909.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3747_30909.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3747_30909.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____30916 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30916 with
           | (univ_names1,uu____30940,typ1) ->
               let uu___3758_30962 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3758_30962.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3758_30962.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3758_30962.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3758_30962.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3758_30962.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30992 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30992 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____31017 =
                            let uu____31018 =
                              let uu____31019 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____31019  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____31018
                             in
                          elim_delayed_subst_term uu____31017  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3774_31022 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3774_31022.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3774_31022.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3774_31022.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3774_31022.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3777_31023 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3777_31023.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3777_31023.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3777_31023.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3777_31023.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3777_31023.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3781_31030 = s  in
          let uu____31031 =
            let uu____31032 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____31032  in
          {
            FStar_Syntax_Syntax.sigel = uu____31031;
            FStar_Syntax_Syntax.sigrng =
              (uu___3781_31030.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3781_31030.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3781_31030.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3781_31030.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3781_31030.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____31036 = elim_uvars_aux_t env us [] t  in
          (match uu____31036 with
           | (us1,uu____31060,t1) ->
               let uu___3792_31082 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3792_31082.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3792_31082.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3792_31082.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3792_31082.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3792_31082.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____31084 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____31084 with
           | (univs1,binders,uu____31103) ->
               let uu____31124 =
                 let uu____31129 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____31129 with
                 | (univs_opening,univs2) ->
                     let uu____31152 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____31152)
                  in
               (match uu____31124 with
                | (univs_opening,univs_closing) ->
                    let uu____31155 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____31161 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____31162 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____31161, uu____31162)  in
                    (match uu____31155 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____31188 =
                           match uu____31188 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____31206 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____31206 with
                                | (us1,t1) ->
                                    let uu____31217 =
                                      let uu____31226 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____31231 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____31226, uu____31231)  in
                                    (match uu____31217 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____31254 =
                                           let uu____31263 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____31268 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____31263, uu____31268)  in
                                         (match uu____31254 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____31292 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____31292
                                                 in
                                              let uu____31293 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____31293 with
                                               | (uu____31320,uu____31321,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____31344 =
                                                       let uu____31345 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____31345
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____31344
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____31354 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____31354 with
                           | (uu____31373,uu____31374,t1) -> t1  in
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
                             | uu____31450 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____31477 =
                               let uu____31478 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____31478.FStar_Syntax_Syntax.n  in
                             match uu____31477 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____31537 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31571 =
                               let uu____31572 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31572.FStar_Syntax_Syntax.n  in
                             match uu____31571 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31595) ->
                                 let uu____31620 = destruct_action_body body
                                    in
                                 (match uu____31620 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31669 ->
                                 let uu____31670 = destruct_action_body t  in
                                 (match uu____31670 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31725 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31725 with
                           | (action_univs,t) ->
                               let uu____31734 = destruct_action_typ_templ t
                                  in
                               (match uu____31734 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3876_31781 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3876_31781.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3876_31781.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3879_31783 = ed  in
                           let uu____31784 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____31785 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____31786 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3879_31783.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3879_31783.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31784;
                             FStar_Syntax_Syntax.combinators = uu____31785;
                             FStar_Syntax_Syntax.actions = uu____31786;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3879_31783.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3882_31789 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3882_31789.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3882_31789.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3882_31789.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3882_31789.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3882_31789.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31810 =
            match uu___19_31810 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____31841 = elim_uvars_aux_t env us [] t  in
                (match uu____31841 with
                 | (us1,uu____31873,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3897_31904 = sub_eff  in
            let uu____31905 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____31908 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3897_31904.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3897_31904.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31905;
              FStar_Syntax_Syntax.lift = uu____31908
            }  in
          let uu___3900_31911 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3900_31911.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3900_31911.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3900_31911.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3900_31911.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3900_31911.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____31921 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____31921 with
           | (univ_names1,binders1,comp1) ->
               let uu___3913_31961 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3913_31961.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3913_31961.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3913_31961.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3913_31961.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3913_31961.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31964 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31965 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n1,p,(us_t,t),(us_ty,ty))
          ->
          let uu____31995 = elim_uvars_aux_t env us_t [] t  in
          (match uu____31995 with
           | (us_t1,uu____32019,t1) ->
               let uu____32041 = elim_uvars_aux_t env us_ty [] ty  in
               (match uu____32041 with
                | (us_ty1,uu____32065,ty1) ->
                    let uu___3938_32087 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n1, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3938_32087.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3938_32087.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3938_32087.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3938_32087.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3938_32087.FStar_Syntax_Syntax.sigopts)
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
        let uu____32138 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____32138 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____32160 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____32160 with
             | (uu____32167,head_def) ->
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
      let uu____32173 = FStar_Syntax_Util.head_and_args t  in
      match uu____32173 with
      | (head1,args) ->
          let uu____32218 =
            let uu____32219 = FStar_Syntax_Subst.compress head1  in
            uu____32219.FStar_Syntax_Syntax.n  in
          (match uu____32218 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____32226;
                  FStar_Syntax_Syntax.vars = uu____32227;_},us)
               -> aux fv us args
           | uu____32233 -> FStar_Pervasives_Native.None)
  