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
  
let rec (is_wp_req_ens_commutation :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun t  ->
      let is_fv t1 lid =
        let uu____9454 =
          let uu____9455 = FStar_Syntax_Subst.compress t1  in
          uu____9455.FStar_Syntax_Syntax.n  in
        match uu____9454 with
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____9460) ->
            let uu____9465 =
              let uu____9466 = FStar_Syntax_Subst.compress t2  in
              uu____9466.FStar_Syntax_Syntax.n  in
            (match uu____9465 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 FStar_Syntax_Syntax.fv_eq_lid fv lid
             | uu____9471 -> false)
        | uu____9473 -> false  in
      let us_of t1 =
        let uu____9481 =
          let uu____9482 = FStar_Syntax_Subst.compress t1  in
          uu____9482.FStar_Syntax_Syntax.n  in
        match uu____9481 with
        | FStar_Syntax_Syntax.Tm_uinst (uu____9485,us) -> us
        | uu____9491 -> failwith "Impossible"  in
      let mk_app1 lid us args r =
        let uu____9514 =
          let uu____9515 =
            let uu____9516 =
              FStar_Syntax_Syntax.lid_as_fv lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                FStar_Pervasives_Native.None
               in
            FStar_All.pipe_right uu____9516 FStar_Syntax_Syntax.fv_to_tm  in
          FStar_All.pipe_right uu____9515
            (fun t1  -> FStar_Syntax_Syntax.mk_Tm_uinst t1 us)
           in
        FStar_All.pipe_right uu____9514
          (fun f  ->
             FStar_Syntax_Syntax.mk_Tm_app f args
               FStar_Pervasives_Native.None r)
         in
      let reduce_as_requires args r =
        let uu____9539 = args  in
        match uu____9539 with
        | uu____9542::(wp,uu____9544)::[] ->
            let uu____9585 =
              let uu____9586 = FStar_Syntax_Subst.compress wp  in
              uu____9586.FStar_Syntax_Syntax.n  in
            (match uu____9585 with
             | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                 is_fv head1 FStar_Parser_Const.as_wp ->
                 let uu____9617 = args1  in
                 (match uu____9617 with
                  | uu____9630::(req,uu____9632)::uu____9633::[] ->
                      FStar_Pervasives_Native.Some req)
             | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                 is_fv head1 FStar_Parser_Const.pure_weaken_wp_lid ->
                 let uu____9716 =
                   let uu____9717 = us_of head1  in
                   mk_app1 FStar_Parser_Const.as_req_weaken uu____9717 args1
                     r
                    in
                 FStar_All.pipe_left
                   (fun _9720  -> FStar_Pervasives_Native.Some _9720)
                   uu____9716
             | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                 is_fv head1 FStar_Parser_Const.pure_strengthen_wp_lid ->
                 let uu____9747 =
                   let uu____9748 = us_of head1  in
                   mk_app1 FStar_Parser_Const.as_req_strengthen uu____9748
                     args1 r
                    in
                 FStar_All.pipe_left
                   (fun _9751  -> FStar_Pervasives_Native.Some _9751)
                   uu____9747
             | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                 is_fv head1 FStar_Parser_Const.pure_bind_lid ->
                 let uu____9778 =
                   let uu____9779 = us_of head1  in
                   let uu____9780 = FStar_All.pipe_right args1 FStar_List.tl
                      in
                   mk_app1 FStar_Parser_Const.as_req_bind uu____9779
                     uu____9780 r
                    in
                 FStar_All.pipe_left
                   (fun _9801  -> FStar_Pervasives_Native.Some _9801)
                   uu____9778
             | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                 is_fv head1 FStar_Parser_Const.pure_if_then_else_lid ->
                 let uu____9828 =
                   let uu____9829 = us_of head1  in
                   mk_app1 FStar_Parser_Const.as_req_if_then_else uu____9829
                     args1 r
                    in
                 FStar_All.pipe_left
                   (fun _9832  -> FStar_Pervasives_Native.Some _9832)
                   uu____9828
             | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                 is_fv head1 FStar_Parser_Const.pure_ite_lid ->
                 let uu____9859 =
                   let uu____9860 = us_of head1  in
                   mk_app1 FStar_Parser_Const.as_req_ite uu____9860 args1 r
                    in
                 FStar_All.pipe_left
                   (fun _9863  -> FStar_Pervasives_Native.Some _9863)
                   uu____9859
             | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                 is_fv head1 FStar_Parser_Const.pure_close_lid ->
                 let uu____9890 =
                   let uu____9891 = us_of head1  in
                   mk_app1 FStar_Parser_Const.as_req_close uu____9891 args1 r
                    in
                 FStar_All.pipe_left
                   (fun _9894  -> FStar_Pervasives_Native.Some _9894)
                   uu____9890
             | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                 is_fv head1 FStar_Parser_Const.pure_null_lid ->
                 let uu____9921 =
                   let uu____9922 = us_of head1  in
                   mk_app1 FStar_Parser_Const.as_req_null uu____9922 args1 r
                    in
                 FStar_All.pipe_left
                   (fun _9925  -> FStar_Pervasives_Native.Some _9925)
                   uu____9921
             | uu____9926 -> FStar_Pervasives_Native.None)
         in
      let reduce_as_ensures args r =
        let wp =
          if (FStar_List.length args) = (Prims.of_int (2))
          then
            let uu____9954 = args  in
            match uu____9954 with | uu____9955::(wp,uu____9957)::[] -> wp
          else
            (let uu____10000 = args  in
             match uu____10000 with
             | uu____10001::(wp,uu____10003)::uu____10004::[] -> wp)
           in
        let uu____10061 =
          let uu____10062 = FStar_Syntax_Subst.compress wp  in
          uu____10062.FStar_Syntax_Syntax.n  in
        match uu____10061 with
        | FStar_Syntax_Syntax.Tm_app (head1,args1) when
            is_fv head1 FStar_Parser_Const.as_wp ->
            let uu____10093 = args1  in
            (match uu____10093 with
             | uu____10106::uu____10107::(ens,uu____10109)::[] ->
                 FStar_Pervasives_Native.Some ens)
        | FStar_Syntax_Syntax.Tm_app (head1,args1) when
            is_fv head1 FStar_Parser_Const.pure_weaken_wp_lid ->
            let uu____10192 =
              let uu____10193 = us_of head1  in
              mk_app1 FStar_Parser_Const.as_ens_weaken uu____10193 args1 r
               in
            FStar_All.pipe_left
              (fun _10196  -> FStar_Pervasives_Native.Some _10196)
              uu____10192
        | FStar_Syntax_Syntax.Tm_app (head1,args1) when
            is_fv head1 FStar_Parser_Const.pure_strengthen_wp_lid ->
            let uu____10223 =
              let uu____10224 = us_of head1  in
              mk_app1 FStar_Parser_Const.as_ens_strengthen uu____10224 args1
                r
               in
            FStar_All.pipe_left
              (fun _10227  -> FStar_Pervasives_Native.Some _10227)
              uu____10223
        | FStar_Syntax_Syntax.Tm_app (head1,args1) when
            is_fv head1 FStar_Parser_Const.pure_bind_lid ->
            let uu____10254 =
              let uu____10255 = us_of head1  in
              let uu____10256 = FStar_All.pipe_right args1 FStar_List.tl  in
              mk_app1 FStar_Parser_Const.as_ens_bind uu____10255 uu____10256
                r
               in
            FStar_All.pipe_left
              (fun _10277  -> FStar_Pervasives_Native.Some _10277)
              uu____10254
        | FStar_Syntax_Syntax.Tm_app (head1,args1) when
            is_fv head1 FStar_Parser_Const.pure_if_then_else_lid ->
            let uu____10304 =
              let uu____10305 = us_of head1  in
              mk_app1 FStar_Parser_Const.as_ens_if_then_else uu____10305
                args1 r
               in
            FStar_All.pipe_left
              (fun _10308  -> FStar_Pervasives_Native.Some _10308)
              uu____10304
        | FStar_Syntax_Syntax.Tm_app (head1,args1) when
            is_fv head1 FStar_Parser_Const.pure_ite_lid ->
            let uu____10335 =
              let uu____10336 = us_of head1  in
              mk_app1 FStar_Parser_Const.as_ens_ite uu____10336 args1 r  in
            FStar_All.pipe_left
              (fun _10339  -> FStar_Pervasives_Native.Some _10339)
              uu____10335
        | FStar_Syntax_Syntax.Tm_app (head1,args1) when
            is_fv head1 FStar_Parser_Const.pure_close_lid ->
            let uu____10366 =
              let uu____10367 = us_of head1  in
              mk_app1 FStar_Parser_Const.as_ens_close uu____10367 args1 r  in
            FStar_All.pipe_left
              (fun _10370  -> FStar_Pervasives_Native.Some _10370)
              uu____10366
        | FStar_Syntax_Syntax.Tm_app (head1,args1) when
            is_fv head1 FStar_Parser_Const.pure_null_lid ->
            let uu____10397 =
              let uu____10398 = us_of head1  in
              mk_app1 FStar_Parser_Const.as_ens_null uu____10398 args1 r  in
            FStar_All.pipe_left
              (fun _10401  -> FStar_Pervasives_Native.Some _10401)
              uu____10397
        | uu____10402 -> FStar_Pervasives_Native.None  in
      let t0 = t  in
      let uu____10404 =
        FStar_All.pipe_left
          (FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv)
          (FStar_Options.Other "WPReqEns")
         in
      if uu____10404
      then
        ((let uu____10412 = FStar_Syntax_Print.term_to_string t  in
          FStar_Util.print1 "Trying to check commutation for: %s\n\n"
            uu____10412);
         (let uu____10415 =
            let uu____10416 = FStar_Syntax_Subst.compress t  in
            uu____10416.FStar_Syntax_Syntax.n  in
          match uu____10415 with
          | FStar_Syntax_Syntax.Tm_app (head1,args) when
              is_fv head1 FStar_Parser_Const.as_requires ->
              reduce_as_requires args t.FStar_Syntax_Syntax.pos
          | FStar_Syntax_Syntax.Tm_app (head1,args) when
              is_fv head1 FStar_Parser_Const.as_ensures ->
              reduce_as_ensures args t.FStar_Syntax_Syntax.pos
          | uu____10473 -> FStar_Pervasives_Native.None))
      else FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____10754 ->
                   let uu____10777 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____10777
               | uu____10780 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____10790  ->
               let uu____10791 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____10793 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____10795 = FStar_Syntax_Print.term_to_string t1  in
               let uu____10797 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____10805 =
                 let uu____10807 =
                   let uu____10810 = firstn (Prims.of_int (4)) stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____10810
                    in
                 stack_to_string uu____10807  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____10791 uu____10793 uu____10795 uu____10797 uu____10805);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____10838  ->
               let uu____10839 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____10839);
          (let t_opt = is_wp_req_ens_commutation cfg t1  in
           let uu____10845 = FStar_All.pipe_right t_opt FStar_Util.is_some
              in
           if uu____10845
           then
             ((let uu____10852 =
                 FStar_All.pipe_left
                   (FStar_TypeChecker_Env.debug
                      cfg.FStar_TypeChecker_Cfg.tcenv)
                   (FStar_Options.Other "WPReqEns")
                  in
               if uu____10852
               then
                 let uu____10857 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____10859 =
                   let uu____10861 =
                     FStar_All.pipe_right t_opt FStar_Util.must  in
                   FStar_All.pipe_right uu____10861
                     FStar_Syntax_Print.term_to_string
                    in
                 FStar_Util.print2
                   "Norm request identified as wp_req_ens commutation, reduced %s to %s\n"
                   uu____10857 uu____10859
               else ());
              (let cfg0 = cfg  in
               let t2 =
                 let uu____10870 =
                   FStar_TypeChecker_Cfg.config' []
                     [FStar_TypeChecker_Env.UnfoldAttr
                        [FStar_Parser_Const.wp_req_ens_attr];
                     FStar_TypeChecker_Env.Beta]
                     cfg.FStar_TypeChecker_Cfg.tcenv
                    in
                 let uu____10871 = FStar_All.pipe_right t_opt FStar_Util.must
                    in
                 norm uu____10870 env [] uu____10871  in
               (let uu____10875 =
                  FStar_All.pipe_left
                    (FStar_TypeChecker_Env.debug
                       cfg.FStar_TypeChecker_Cfg.tcenv)
                    (FStar_Options.Other "WPReqEns")
                   in
                if uu____10875
                then
                  let uu____10880 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print1
                    "After restricted normalization, t : %s\n" uu____10880
                else ());
               norm cfg0 env stack t2))
           else
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10890  ->
                        let uu____10891 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10891);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_constant uu____10894 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10898  ->
                        let uu____10899 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10899);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_name uu____10902 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10906  ->
                        let uu____10907 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10907);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_lazy uu____10910 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10914  ->
                        let uu____10915 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10915);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = uu____10918;
                    FStar_Syntax_Syntax.fv_delta = uu____10919;
                    FStar_Syntax_Syntax.fv_qual =
                      FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Data_ctor );_}
                  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10923  ->
                        let uu____10924 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10924);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = uu____10927;
                    FStar_Syntax_Syntax.fv_delta = uu____10928;
                    FStar_Syntax_Syntax.fv_qual =
                      FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor uu____10929);_}
                  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____10939  ->
                        let uu____10940 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____10940);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                  let qninfo =
                    FStar_TypeChecker_Env.lookup_qname
                      cfg.FStar_TypeChecker_Cfg.tcenv lid
                     in
                  let uu____10946 =
                    FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
                  (match uu____10946 with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Delta_constant_at_level _10949)
                       when _10949 = Prims.int_zero ->
                       (FStar_TypeChecker_Cfg.log_unfolding cfg
                          (fun uu____10953  ->
                             let uu____10954 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                               uu____10954);
                        rebuild cfg env stack t1)
                   | uu____10957 ->
                       let uu____10960 =
                         decide_unfolding cfg env stack
                           t1.FStar_Syntax_Syntax.pos fv qninfo
                          in
                       (match uu____10960 with
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
                  let uu____10999 = closure_as_term cfg env t2  in
                  rebuild cfg env stack uu____10999
              | FStar_Syntax_Syntax.Tm_app (hd1,args) when
                  (should_consider_norm_requests cfg) &&
                    (let uu____11027 = is_norm_request hd1 args  in
                     uu____11027 = Norm_request_requires_rejig)
                  ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     FStar_Util.print_string "Rejigging norm request ... \n"
                   else ();
                   (let uu____11033 = rejig_norm_request hd1 args  in
                    norm cfg env stack uu____11033))
              | FStar_Syntax_Syntax.Tm_app (hd1,args) when
                  (should_consider_norm_requests cfg) &&
                    (let uu____11061 = is_norm_request hd1 args  in
                     uu____11061 = Norm_request_ready)
                  ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     FStar_Util.print_string "Potential norm request ... \n"
                   else ();
                   (let cfg' =
                      let uu___1410_11068 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (let uu___1412_11071 =
                             cfg.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               false;
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1412_11071.FStar_TypeChecker_Cfg.for_extraction)
                           });
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1410_11068.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1410_11068.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          [FStar_TypeChecker_Env.Unfold
                             FStar_Syntax_Syntax.delta_constant];
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1410_11068.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1410_11068.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1410_11068.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___1410_11068.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let uu____11078 =
                      get_norm_request cfg (norm cfg' env []) args  in
                    match uu____11078 with
                    | FStar_Pervasives_Native.None  ->
                        (if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           FStar_Util.print_string "Norm request None ... \n"
                         else ();
                         (let stack1 =
                            FStar_All.pipe_right stack
                              (FStar_List.fold_right
                                 (fun uu____11114  ->
                                    fun stack1  ->
                                      match uu____11114 with
                                      | (a,aq) ->
                                          let uu____11126 =
                                            let uu____11127 =
                                              let uu____11134 =
                                                let uu____11135 =
                                                  let uu____11167 =
                                                    FStar_Util.mk_ref
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  (env, a, uu____11167,
                                                    false)
                                                   in
                                                Clos uu____11135  in
                                              (uu____11134, aq,
                                                (t1.FStar_Syntax_Syntax.pos))
                                               in
                                            Arg uu____11127  in
                                          uu____11126 :: stack1) args)
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____11235  ->
                               let uu____11236 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length args)
                                  in
                               FStar_Util.print1 "\tPushed %s arguments\n"
                                 uu____11236);
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
                            let uu____11268 =
                              let uu____11270 =
                                let uu____11272 =
                                  FStar_Util.time_diff start fin  in
                                FStar_Pervasives_Native.snd uu____11272  in
                              FStar_Util.string_of_int uu____11270  in
                            let uu____11279 =
                              FStar_Syntax_Print.term_to_string tm'  in
                            let uu____11281 =
                              FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                            let uu____11283 =
                              FStar_Syntax_Print.term_to_string tm_norm  in
                            FStar_Util.print4
                              "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                              uu____11268 uu____11279 uu____11281 uu____11283)
                         else ();
                         rebuild cfg env stack tm_norm)
                    | FStar_Pervasives_Native.Some (s,tm) ->
                        let delta_level =
                          let uu____11303 =
                            FStar_All.pipe_right s
                              (FStar_Util.for_some
                                 (fun uu___13_11310  ->
                                    match uu___13_11310 with
                                    | FStar_TypeChecker_Env.UnfoldUntil
                                        uu____11312 -> true
                                    | FStar_TypeChecker_Env.UnfoldOnly
                                        uu____11314 -> true
                                    | FStar_TypeChecker_Env.UnfoldFully
                                        uu____11318 -> true
                                    | uu____11322 -> false))
                             in
                          if uu____11303
                          then
                            [FStar_TypeChecker_Env.Unfold
                               FStar_Syntax_Syntax.delta_constant]
                          else [FStar_TypeChecker_Env.NoDelta]  in
                        let cfg'1 =
                          let uu___1450_11330 = cfg  in
                          let uu____11331 =
                            let uu___1452_11332 =
                              FStar_TypeChecker_Cfg.to_fsteps s  in
                            {
                              FStar_TypeChecker_Cfg.beta =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.beta);
                              FStar_TypeChecker_Cfg.iota =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.iota);
                              FStar_TypeChecker_Cfg.zeta =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.zeta);
                              FStar_TypeChecker_Cfg.weak =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.weak);
                              FStar_TypeChecker_Cfg.hnf =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.hnf);
                              FStar_TypeChecker_Cfg.primops =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.primops);
                              FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                              FStar_TypeChecker_Cfg.unfold_until =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.unfold_until);
                              FStar_TypeChecker_Cfg.unfold_only =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.unfold_only);
                              FStar_TypeChecker_Cfg.unfold_fully =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.unfold_fully);
                              FStar_TypeChecker_Cfg.unfold_attr =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.unfold_attr);
                              FStar_TypeChecker_Cfg.unfold_tac =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.unfold_tac);
                              FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                              FStar_TypeChecker_Cfg.simplify =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.simplify);
                              FStar_TypeChecker_Cfg.erase_universes =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.erase_universes);
                              FStar_TypeChecker_Cfg.allow_unbound_universes =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.allow_unbound_universes);
                              FStar_TypeChecker_Cfg.reify_ =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.reify_);
                              FStar_TypeChecker_Cfg.compress_uvars =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.compress_uvars);
                              FStar_TypeChecker_Cfg.no_full_norm =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.no_full_norm);
                              FStar_TypeChecker_Cfg.check_no_uvars =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.check_no_uvars);
                              FStar_TypeChecker_Cfg.unmeta =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.unmeta);
                              FStar_TypeChecker_Cfg.unascribe =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.unascribe);
                              FStar_TypeChecker_Cfg.in_full_norm_request =
                                true;
                              FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                              FStar_TypeChecker_Cfg.nbe_step =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.nbe_step);
                              FStar_TypeChecker_Cfg.for_extraction =
                                (uu___1452_11332.FStar_TypeChecker_Cfg.for_extraction)
                            }  in
                          {
                            FStar_TypeChecker_Cfg.steps = uu____11331;
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___1450_11330.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___1450_11330.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level = delta_level;
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___1450_11330.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___1450_11330.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___1450_11330.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                            FStar_TypeChecker_Cfg.reifying =
                              (uu___1450_11330.FStar_TypeChecker_Cfg.reifying)
                          }  in
                        let stack' =
                          let tail1 = (Cfg cfg) :: stack  in
                          if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                          then
                            let uu____11340 =
                              let uu____11341 =
                                let uu____11346 = FStar_Util.now ()  in
                                (tm, uu____11346)  in
                              Debug uu____11341  in
                            uu____11340 :: tail1
                          else tail1  in
                        norm cfg'1 env stack' tm))
              | FStar_Syntax_Syntax.Tm_type u ->
                  let u1 = norm_universe cfg env u  in
                  let uu____11351 =
                    mk (FStar_Syntax_Syntax.Tm_type u1)
                      t1.FStar_Syntax_Syntax.pos
                     in
                  rebuild cfg env stack uu____11351
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                  then norm cfg env stack t'
                  else
                    (let us1 =
                       let uu____11362 =
                         let uu____11369 =
                           FStar_List.map (norm_universe cfg env) us  in
                         (uu____11369, (t1.FStar_Syntax_Syntax.pos))  in
                       UnivArgs uu____11362  in
                     let stack1 = us1 :: stack  in norm cfg env stack1 t')
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____11378 = lookup_bvar env x  in
                  (match uu____11378 with
                   | Univ uu____11379 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> failwith "Term variable not found"
                   | Clos (env1,t0,r,fix) ->
                       if
                         (Prims.op_Negation fix) ||
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                       then
                         let uu____11433 = FStar_ST.op_Bang r  in
                         (match uu____11433 with
                          | FStar_Pervasives_Native.Some (env2,t') ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11529  ->
                                    let uu____11530 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____11532 =
                                      FStar_Syntax_Print.term_to_string t'
                                       in
                                    FStar_Util.print2
                                      "Lazy hit: %s cached to %s\n"
                                      uu____11530 uu____11532);
                               (let uu____11535 = maybe_weakly_reduced t'  in
                                if uu____11535
                                then
                                  match stack with
                                  | [] when
                                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                        ||
                                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                      -> rebuild cfg env2 stack t'
                                  | uu____11538 -> norm cfg env2 stack t'
                                else rebuild cfg env2 stack t'))
                          | FStar_Pervasives_Native.None  ->
                              norm cfg env1 ((MemoLazy r) :: stack) t0)
                       else norm cfg env1 stack t0)
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  (match stack with
                   | (UnivArgs uu____11582)::uu____11583 ->
                       failwith
                         "Ill-typed term: universes cannot be applied to term abstraction"
                   | (Arg (c,uu____11594,uu____11595))::stack_rest ->
                       (match c with
                        | Univ uu____11599 ->
                            norm cfg ((FStar_Pervasives_Native.None, c) ::
                              env) stack_rest t1
                        | uu____11608 ->
                            (match bs with
                             | [] -> failwith "Impossible"
                             | b::[] ->
                                 (FStar_TypeChecker_Cfg.log cfg
                                    (fun uu____11638  ->
                                       let uu____11639 = closure_to_string c
                                          in
                                       FStar_Util.print1 "\tShifted %s\n"
                                         uu____11639);
                                  norm cfg
                                    (((FStar_Pervasives_Native.Some b), c) ::
                                    env) stack_rest body)
                             | b::tl1 ->
                                 (FStar_TypeChecker_Cfg.log cfg
                                    (fun uu____11675  ->
                                       let uu____11676 = closure_to_string c
                                          in
                                       FStar_Util.print1 "\tShifted %s\n"
                                         uu____11676);
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
                          (fun uu____11724  ->
                             let uu____11725 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.print1 "\tSet memo %s\n" uu____11725);
                        norm cfg env stack1 t1)
                   | (Match uu____11728)::uu____11729 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____11744 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____11744 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____11780  -> dummy :: env1)
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
                                             let uu____11824 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____11824)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1570_11832 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1570_11832.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1570_11832.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____11833 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11839  ->
                                    let uu____11840 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____11840);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1577_11855 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1577_11855.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1577_11855.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1577_11855.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1577_11855.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1577_11855.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1577_11855.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1577_11855.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1577_11855.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Debug uu____11859)::uu____11860 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____11871 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____11871 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____11907  -> dummy :: env1)
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
                                             let uu____11951 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____11951)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1570_11959 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1570_11959.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1570_11959.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____11960 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11966  ->
                                    let uu____11967 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____11967);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1577_11982 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1577_11982.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1577_11982.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1577_11982.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1577_11982.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1577_11982.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1577_11982.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1577_11982.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1577_11982.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Meta uu____11986)::uu____11987 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12000 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12000 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12036  -> dummy :: env1)
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
                                             let uu____12080 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12080)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1570_12088 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1570_12088.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1570_12088.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12089 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12095  ->
                                    let uu____12096 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12096);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1577_12111 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1577_12111.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1577_12111.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1577_12111.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1577_12111.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1577_12111.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1577_12111.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1577_12111.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1577_12111.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Let uu____12115)::uu____12116 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12131 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12131 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12167  -> dummy :: env1)
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
                                             let uu____12211 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12211)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1570_12219 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1570_12219.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1570_12219.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12220 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12226  ->
                                    let uu____12227 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12227);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1577_12242 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1577_12242.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1577_12242.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1577_12242.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1577_12242.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1577_12242.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1577_12242.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1577_12242.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1577_12242.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (App uu____12246)::uu____12247 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12262 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12262 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12298  -> dummy :: env1)
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
                                             let uu____12342 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12342)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1570_12350 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1570_12350.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1570_12350.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12351 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12357  ->
                                    let uu____12358 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12358);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1577_12373 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1577_12373.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1577_12373.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1577_12373.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1577_12373.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1577_12373.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1577_12373.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1577_12373.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1577_12373.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Abs uu____12377)::uu____12378 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12397 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12397 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12433  -> dummy :: env1)
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
                                             let uu____12477 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12477)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1570_12485 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1570_12485.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1570_12485.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12486 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12492  ->
                                    let uu____12493 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12493);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1577_12508 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1577_12508.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1577_12508.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1577_12508.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1577_12508.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1577_12508.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1577_12508.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1577_12508.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1577_12508.FStar_TypeChecker_Cfg.reifying)
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
                         (let uu____12516 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12516 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12552  -> dummy :: env1)
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
                                             let uu____12596 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12596)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1570_12604 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1570_12604.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1570_12604.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12605 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12611  ->
                                    let uu____12612 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12612);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1577_12627 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1577_12627.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1577_12627.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1577_12627.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1577_12627.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1577_12627.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1577_12627.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1577_12627.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1577_12627.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1))))
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let strict_args =
                    let uu____12663 =
                      let uu____12664 = FStar_Syntax_Util.un_uinst head1  in
                      uu____12664.FStar_Syntax_Syntax.n  in
                    match uu____12663 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_TypeChecker_Env.fv_has_strict_args
                          cfg.FStar_TypeChecker_Cfg.tcenv fv
                    | uu____12673 -> FStar_Pervasives_Native.None  in
                  (match strict_args with
                   | FStar_Pervasives_Native.None  ->
                       let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____12694  ->
                                 fun stack1  ->
                                   match uu____12694 with
                                   | (a,aq) ->
                                       let uu____12706 =
                                         let uu____12707 =
                                           let uu____12714 =
                                             let uu____12715 =
                                               let uu____12747 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____12747, false)
                                                in
                                             Clos uu____12715  in
                                           (uu____12714, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____12707  in
                                       uu____12706 :: stack1) args)
                          in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____12815  ->
                             let uu____12816 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length args)
                                in
                             FStar_Util.print1 "\tPushed %s arguments\n"
                               uu____12816);
                        norm cfg env stack1 head1)
                   | FStar_Pervasives_Native.Some strict_args1 ->
                       let norm_args =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____12867  ->
                                 match uu____12867 with
                                 | (a,i) ->
                                     let uu____12878 = norm cfg env [] a  in
                                     (uu____12878, i)))
                          in
                       let norm_args_len = FStar_List.length norm_args  in
                       let uu____12884 =
                         FStar_All.pipe_right strict_args1
                           (FStar_List.for_all
                              (fun i  ->
                                 if i >= norm_args_len
                                 then false
                                 else
                                   (let uu____12899 =
                                      FStar_List.nth norm_args i  in
                                    match uu____12899 with
                                    | (arg_i,uu____12910) ->
                                        let uu____12911 =
                                          FStar_Syntax_Util.head_and_args
                                            arg_i
                                           in
                                        (match uu____12911 with
                                         | (head2,uu____12930) ->
                                             let uu____12955 =
                                               let uu____12956 =
                                                 FStar_Syntax_Util.un_uinst
                                                   head2
                                                  in
                                               uu____12956.FStar_Syntax_Syntax.n
                                                in
                                             (match uu____12955 with
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____12960 -> true
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv ->
                                                  let uu____12963 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Env.is_datacon
                                                    cfg.FStar_TypeChecker_Cfg.tcenv
                                                    uu____12963
                                              | uu____12964 -> false)))))
                          in
                       if uu____12884
                       then
                         let stack1 =
                           FStar_All.pipe_right stack
                             (FStar_List.fold_right
                                (fun uu____12981  ->
                                   fun stack1  ->
                                     match uu____12981 with
                                     | (a,aq) ->
                                         let uu____12993 =
                                           let uu____12994 =
                                             let uu____13001 =
                                               let uu____13002 =
                                                 let uu____13034 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], a))
                                                    in
                                                 (env, a, uu____13034, false)
                                                  in
                                               Clos uu____13002  in
                                             (uu____13001, aq,
                                               (t1.FStar_Syntax_Syntax.pos))
                                              in
                                           Arg uu____12994  in
                                         uu____12993 :: stack1) norm_args)
                            in
                         (FStar_TypeChecker_Cfg.log cfg
                            (fun uu____13116  ->
                               let uu____13117 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length args)
                                  in
                               FStar_Util.print1 "\tPushed %s arguments\n"
                                 uu____13117);
                          norm cfg env stack1 head1)
                       else
                         (let head2 = closure_as_term cfg env head1  in
                          let term =
                            FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                              FStar_Pervasives_Native.None
                              t1.FStar_Syntax_Syntax.pos
                             in
                          rebuild cfg env stack term))
              | FStar_Syntax_Syntax.Tm_refine (x,uu____13137) when
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
                                ((let uu___1639_13182 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1639_13182.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1639_13182.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t_x
                                  }), f)) t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild cfg env stack t2
                     | uu____13183 ->
                         let uu____13198 = closure_as_term cfg env t1  in
                         rebuild cfg env stack uu____13198)
                  else
                    (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                     let uu____13202 =
                       FStar_Syntax_Subst.open_term
                         [(x, FStar_Pervasives_Native.None)] f
                        in
                     match uu____13202 with
                     | (closing,f1) ->
                         let f2 = norm cfg (dummy :: env) [] f1  in
                         let t2 =
                           let uu____13233 =
                             let uu____13234 =
                               let uu____13241 =
                                 FStar_Syntax_Subst.close closing f2  in
                               ((let uu___1648_13247 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1648_13247.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1648_13247.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t_x
                                 }), uu____13241)
                                in
                             FStar_Syntax_Syntax.Tm_refine uu____13234  in
                           mk uu____13233 t1.FStar_Syntax_Syntax.pos  in
                         rebuild cfg env stack t2)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                  then
                    let uu____13271 = closure_as_term cfg env t1  in
                    rebuild cfg env stack uu____13271
                  else
                    (let uu____13274 = FStar_Syntax_Subst.open_comp bs c  in
                     match uu____13274 with
                     | (bs1,c1) ->
                         let c2 =
                           let uu____13282 =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13308  -> dummy :: env1) env)
                              in
                           norm_comp cfg uu____13282 c1  in
                         let t2 =
                           let uu____13332 = norm_binders cfg env bs1  in
                           FStar_Syntax_Util.arrow uu____13332 c2  in
                         rebuild cfg env stack t2)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
                  -> norm cfg env stack t11
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
                  (match stack with
                   | (Match uu____13445)::uu____13446 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13459  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (Arg uu____13461)::uu____13462 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13473  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (App
                       (uu____13475,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_reify );
                                      FStar_Syntax_Syntax.pos = uu____13476;
                                      FStar_Syntax_Syntax.vars = uu____13477;_},uu____13478,uu____13479))::uu____13480
                       when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13487  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (MemoLazy uu____13489)::uu____13490 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13501  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | uu____13503 ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13506  ->
                             FStar_Util.print_string
                               "+++ Keeping ascription \n");
                        (let t12 = norm cfg env [] t11  in
                         FStar_TypeChecker_Cfg.log cfg
                           (fun uu____13511  ->
                              FStar_Util.print_string
                                "+++ Normalizing ascription \n");
                         (let tc1 =
                            match tc with
                            | FStar_Util.Inl t2 ->
                                let uu____13537 = norm cfg env [] t2  in
                                FStar_Util.Inl uu____13537
                            | FStar_Util.Inr c ->
                                let uu____13551 = norm_comp cfg env c  in
                                FStar_Util.Inr uu____13551
                             in
                          let tacopt1 =
                            FStar_Util.map_opt tacopt (norm cfg env [])  in
                          match stack with
                          | (Cfg cfg1)::stack1 ->
                              let t2 =
                                let uu____13574 =
                                  let uu____13575 =
                                    let uu____13602 =
                                      FStar_Syntax_Util.unascribe t12  in
                                    (uu____13602, (tc1, tacopt1), l)  in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____13575
                                   in
                                mk uu____13574 t1.FStar_Syntax_Syntax.pos  in
                              norm cfg1 env stack1 t2
                          | uu____13637 ->
                              let uu____13638 =
                                let uu____13639 =
                                  let uu____13640 =
                                    let uu____13667 =
                                      FStar_Syntax_Util.unascribe t12  in
                                    (uu____13667, (tc1, tacopt1), l)  in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____13640
                                   in
                                mk uu____13639 t1.FStar_Syntax_Syntax.pos  in
                              rebuild cfg env stack uu____13638))))
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
                      let uu___1727_13745 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (let uu___1729_13748 =
                             cfg.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak = true;
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1729_13748.FStar_TypeChecker_Cfg.for_extraction)
                           });
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1727_13745.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1727_13745.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___1727_13745.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1727_13745.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1727_13745.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1727_13745.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___1727_13745.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___1727_13745.FStar_TypeChecker_Cfg.reifying)
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
                            let uu____13789 =
                              FStar_Syntax_Subst.univ_var_opening
                                lb.FStar_Syntax_Syntax.lbunivs
                               in
                            match uu____13789 with
                            | (openings,lbunivs) ->
                                let cfg1 =
                                  let uu___1742_13809 = cfg  in
                                  let uu____13810 =
                                    FStar_TypeChecker_Env.push_univ_vars
                                      cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                     in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1742_13809.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv = uu____13810;
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1742_13809.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1742_13809.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1742_13809.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong =
                                      (uu___1742_13809.FStar_TypeChecker_Cfg.strong);
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1742_13809.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1742_13809.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1742_13809.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                let norm1 t2 =
                                  let uu____13817 =
                                    let uu____13818 =
                                      FStar_Syntax_Subst.subst openings t2
                                       in
                                    norm cfg1 env [] uu____13818  in
                                  FStar_Syntax_Subst.close_univ_vars lbunivs
                                    uu____13817
                                   in
                                let lbtyp =
                                  norm1 lb.FStar_Syntax_Syntax.lbtyp  in
                                let lbdef =
                                  norm1 lb.FStar_Syntax_Syntax.lbdef  in
                                let uu___1749_13821 = lb  in
                                {
                                  FStar_Syntax_Syntax.lbname =
                                    (uu___1749_13821.FStar_Syntax_Syntax.lbname);
                                  FStar_Syntax_Syntax.lbunivs = lbunivs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1749_13821.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = lbdef;
                                  FStar_Syntax_Syntax.lbattrs =
                                    (uu___1749_13821.FStar_Syntax_Syntax.lbattrs);
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1749_13821.FStar_Syntax_Syntax.lbpos)
                                }))
                     in
                  let uu____13822 =
                    mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                      t1.FStar_Syntax_Syntax.pos
                     in
                  rebuild cfg env stack uu____13822
              | FStar_Syntax_Syntax.Tm_let
                  ((uu____13835,{
                                  FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                    uu____13836;
                                  FStar_Syntax_Syntax.lbunivs = uu____13837;
                                  FStar_Syntax_Syntax.lbtyp = uu____13838;
                                  FStar_Syntax_Syntax.lbeff = uu____13839;
                                  FStar_Syntax_Syntax.lbdef = uu____13840;
                                  FStar_Syntax_Syntax.lbattrs = uu____13841;
                                  FStar_Syntax_Syntax.lbpos = uu____13842;_}::uu____13843),uu____13844)
                  -> rebuild cfg env stack t1
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let uu____13889 =
                    FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
                  if uu____13889
                  then
                    let binder =
                      let uu____13893 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.mk_binder uu____13893  in
                    let env1 =
                      let uu____13903 =
                        let uu____13910 =
                          let uu____13911 =
                            let uu____13943 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env, (lb.FStar_Syntax_Syntax.lbdef),
                              uu____13943, false)
                             in
                          Clos uu____13911  in
                        ((FStar_Pervasives_Native.Some binder), uu____13910)
                         in
                      uu____13903 :: env  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____14018  ->
                          FStar_Util.print_string "+++ Reducing Tm_let\n");
                     norm cfg env1 stack body)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____14025  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____14027 = closure_as_term cfg env t1  in
                        rebuild cfg env stack uu____14027))
                    else
                      (let uu____14030 =
                         let uu____14035 =
                           let uu____14036 =
                             let uu____14043 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____14043
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____14036]  in
                         FStar_Syntax_Subst.open_term uu____14035 body  in
                       match uu____14030 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____14070  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____14079 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____14079  in
                               FStar_Util.Inl
                                 (let uu___1790_14095 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1790_14095.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1790_14095.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____14098  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1795_14101 = lb  in
                                let uu____14102 =
                                  norm cfg env []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____14105 =
                                  FStar_List.map (norm cfg env [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1795_14101.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1795_14101.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____14102;
                                  FStar_Syntax_Syntax.lbattrs = uu____14105;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1795_14101.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____14140  -> dummy :: env1)
                                     env)
                                 in
                              let stack1 = (Cfg cfg) :: stack  in
                              let cfg1 =
                                let uu___1802_14165 = cfg  in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1802_14165.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1802_14165.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1802_14165.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1802_14165.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1802_14165.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1802_14165.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1802_14165.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1802_14165.FStar_TypeChecker_Cfg.reifying)
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____14169  ->
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
                  let uu____14190 = FStar_Syntax_Subst.open_let_rec lbs body
                     in
                  (match uu____14190 with
                   | (lbs1,body1) ->
                       let lbs2 =
                         FStar_List.map
                           (fun lb  ->
                              let ty =
                                norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                 in
                              let lbname =
                                let uu____14226 =
                                  let uu___1818_14227 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1818_14227.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1818_14227.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  }  in
                                FStar_Util.Inl uu____14226  in
                              let uu____14228 =
                                FStar_Syntax_Util.abs_formals
                                  lb.FStar_Syntax_Syntax.lbdef
                                 in
                              match uu____14228 with
                              | (xs,def_body,lopt) ->
                                  let xs1 = norm_binders cfg env xs  in
                                  let env1 =
                                    let uu____14254 =
                                      FStar_List.map
                                        (fun uu____14276  -> dummy) xs1
                                       in
                                    let uu____14283 =
                                      let uu____14292 =
                                        FStar_List.map
                                          (fun uu____14308  -> dummy) lbs1
                                         in
                                      FStar_List.append uu____14292 env  in
                                    FStar_List.append uu____14254 uu____14283
                                     in
                                  let def_body1 = norm cfg env1 [] def_body
                                     in
                                  let lopt1 =
                                    match lopt with
                                    | FStar_Pervasives_Native.Some rc ->
                                        let uu____14328 =
                                          let uu___1832_14329 = rc  in
                                          let uu____14330 =
                                            FStar_Util.map_opt
                                              rc.FStar_Syntax_Syntax.residual_typ
                                              (norm cfg env1 [])
                                             in
                                          {
                                            FStar_Syntax_Syntax.residual_effect
                                              =
                                              (uu___1832_14329.FStar_Syntax_Syntax.residual_effect);
                                            FStar_Syntax_Syntax.residual_typ
                                              = uu____14330;
                                            FStar_Syntax_Syntax.residual_flags
                                              =
                                              (uu___1832_14329.FStar_Syntax_Syntax.residual_flags)
                                          }  in
                                        FStar_Pervasives_Native.Some
                                          uu____14328
                                    | uu____14339 -> lopt  in
                                  let def =
                                    FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                     in
                                  let uu___1837_14345 = lb  in
                                  {
                                    FStar_Syntax_Syntax.lbname = lbname;
                                    FStar_Syntax_Syntax.lbunivs =
                                      (uu___1837_14345.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp = ty;
                                    FStar_Syntax_Syntax.lbeff =
                                      (uu___1837_14345.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs =
                                      (uu___1837_14345.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (uu___1837_14345.FStar_Syntax_Syntax.lbpos)
                                  }) lbs1
                          in
                       let env' =
                         let uu____14355 =
                           FStar_List.map (fun uu____14371  -> dummy) lbs2
                            in
                         FStar_List.append uu____14355 env  in
                       let body2 = norm cfg env' [] body1  in
                       let uu____14379 =
                         FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                       (match uu____14379 with
                        | (lbs3,body3) ->
                            let t2 =
                              let uu___1846_14395 = t1  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_let
                                     ((true, lbs3), body3));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1846_14395.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1846_14395.FStar_Syntax_Syntax.vars)
                              }  in
                            rebuild cfg env stack t2))
              | FStar_Syntax_Syntax.Tm_let (lbs,body) when
                  Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                  ->
                  let uu____14429 = closure_as_term cfg env t1  in
                  rebuild cfg env stack uu____14429
              | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
                  let uu____14450 =
                    FStar_List.fold_right
                      (fun lb  ->
                         fun uu____14528  ->
                           match uu____14528 with
                           | (rec_env,memos,i) ->
                               let bv =
                                 let uu___1862_14653 =
                                   FStar_Util.left
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1862_14653.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index = i;
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1862_14653.FStar_Syntax_Syntax.sort)
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
                  (match uu____14450 with
                   | (rec_env,memos,uu____14844) ->
                       let uu____14899 =
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
                                let uu____15148 =
                                  let uu____15155 =
                                    let uu____15156 =
                                      let uu____15188 =
                                        FStar_Util.mk_ref
                                          FStar_Pervasives_Native.None
                                         in
                                      (rec_env,
                                        (lb.FStar_Syntax_Syntax.lbdef),
                                        uu____15188, false)
                                       in
                                    Clos uu____15156  in
                                  (FStar_Pervasives_Native.None, uu____15155)
                                   in
                                uu____15148 :: env1)
                           (FStar_Pervasives_Native.snd lbs) env
                          in
                       norm cfg body_env stack body)
              | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____15273  ->
                        let uu____15274 =
                          FStar_Syntax_Print.metadata_to_string m  in
                        FStar_Util.print1 ">> metadata = %s\n" uu____15274);
                   (match m with
                    | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                        reduce_impure_comp cfg env stack head1
                          (FStar_Util.Inl m1) t2
                    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                        reduce_impure_comp cfg env stack head1
                          (FStar_Util.Inr (m1, m')) t2
                    | uu____15298 ->
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                        then norm cfg env stack head1
                        else
                          (match stack with
                           | uu____15302::uu____15303 ->
                               (match m with
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (l,r,uu____15308) ->
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
                                | uu____15387 -> norm cfg env stack head1)
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
                                     let uu____15435 =
                                       let uu____15456 =
                                         norm_pattern_args cfg env args  in
                                       (names2, uu____15456)  in
                                     FStar_Syntax_Syntax.Meta_pattern
                                       uu____15435
                                 | uu____15485 -> m  in
                               let t2 =
                                 mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                   t1.FStar_Syntax_Syntax.pos
                                  in
                               rebuild cfg env stack t2)))
              | FStar_Syntax_Syntax.Tm_delayed uu____15491 ->
                  let t2 = FStar_Syntax_Subst.compress t1  in
                  norm cfg env stack t2
              | FStar_Syntax_Syntax.Tm_uvar uu____15515 ->
                  let t2 = FStar_Syntax_Subst.compress t1  in
                  (match t2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar uu____15529 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                       then
                         let uu____15543 =
                           let uu____15545 =
                             FStar_Range.string_of_range
                               t2.FStar_Syntax_Syntax.pos
                              in
                           let uu____15547 =
                             FStar_Syntax_Print.term_to_string t2  in
                           FStar_Util.format2
                             "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                             uu____15545 uu____15547
                            in
                         failwith uu____15543
                       else
                         (let uu____15552 = inline_closure_env cfg env [] t2
                             in
                          rebuild cfg env stack uu____15552)
                   | uu____15553 -> norm cfg env stack t2)))

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
              let uu____15562 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____15562 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____15576  ->
                        let uu____15577 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____15577);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____15590  ->
                        let uu____15591 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____15593 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____15591 uu____15593);
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
                      | (UnivArgs (us',uu____15606))::stack1 ->
                          ((let uu____15615 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____15615
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____15623 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____15623) us'
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
                      | uu____15659 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____15662 ->
                          let uu____15665 =
                            let uu____15667 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____15667
                             in
                          failwith uu____15665
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
                  let uu___1974_15695 = cfg  in
                  let uu____15696 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____15696;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1974_15695.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1974_15695.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1974_15695.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1974_15695.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1974_15695.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1974_15695.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1974_15695.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____15727,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____15728;
                                    FStar_Syntax_Syntax.vars = uu____15729;_},uu____15730,uu____15731))::uu____15732
                     -> ()
                 | uu____15737 ->
                     let uu____15740 =
                       let uu____15742 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____15742
                        in
                     failwith uu____15740);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____15751  ->
                      let uu____15752 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____15754 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____15752
                        uu____15754);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____15758 =
                    let uu____15759 = FStar_Syntax_Subst.compress head3  in
                    uu____15759.FStar_Syntax_Syntax.n  in
                  match uu____15758 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____15780 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____15780
                         in
                      let uu____15781 =
                        let uu____15790 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_bind_repr
                           in
                        FStar_All.pipe_right uu____15790 FStar_Util.must  in
                      (match uu____15781 with
                       | (uu____15805,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____15815 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____15826 =
                                    let uu____15827 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____15827.FStar_Syntax_Syntax.n  in
                                  match uu____15826 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____15833,uu____15834))
                                      ->
                                      let uu____15843 =
                                        let uu____15844 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____15844.FStar_Syntax_Syntax.n  in
                                      (match uu____15843 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____15850,msrc,uu____15852))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____15861 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____15861
                                       | uu____15862 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____15863 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____15864 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____15864 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___2046_15869 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___2046_15869.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___2046_15869.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___2046_15869.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___2046_15869.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___2046_15869.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____15870 = FStar_List.tl stack
                                        in
                                     let uu____15871 =
                                       let uu____15872 =
                                         let uu____15879 =
                                           let uu____15880 =
                                             let uu____15894 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____15894)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____15880
                                            in
                                         FStar_Syntax_Syntax.mk uu____15879
                                          in
                                       uu____15872
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____15870 uu____15871
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____15910 =
                                       let uu____15912 = is_return body  in
                                       match uu____15912 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____15917;
                                             FStar_Syntax_Syntax.vars =
                                               uu____15918;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____15921 -> false  in
                                     if uu____15910
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
                                          let uu____15945 =
                                            let uu____15952 =
                                              let uu____15953 =
                                                let uu____15972 =
                                                  let uu____15981 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____15981]  in
                                                (uu____15972, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____15953
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____15952
                                             in
                                          uu____15945
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____16020 =
                                            let uu____16021 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____16021.FStar_Syntax_Syntax.n
                                             in
                                          match uu____16020 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____16027::uu____16028::[])
                                              ->
                                              let uu____16033 =
                                                let uu____16040 =
                                                  let uu____16041 =
                                                    let uu____16048 =
                                                      let uu____16049 =
                                                        let uu____16050 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____16050
                                                         in
                                                      let uu____16051 =
                                                        let uu____16054 =
                                                          let uu____16055 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____16055
                                                           in
                                                        [uu____16054]  in
                                                      uu____16049 ::
                                                        uu____16051
                                                       in
                                                    (bind1, uu____16048)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____16041
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____16040
                                                 in
                                              uu____16033
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____16058 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____16073 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____16073
                                          then
                                            let uu____16086 =
                                              let uu____16095 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____16095
                                               in
                                            let uu____16096 =
                                              let uu____16107 =
                                                let uu____16116 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____16116
                                                 in
                                              [uu____16107]  in
                                            uu____16086 :: uu____16096
                                          else []  in
                                        let reified =
                                          let args =
                                            let uu____16165 =
                                              FStar_Syntax_Util.is_layered ed
                                               in
                                            if uu____16165
                                            then
                                              let unit_args =
                                                let uu____16189 =
                                                  let uu____16190 =
                                                    let uu____16193 =
                                                      let uu____16194 =
                                                        FStar_All.pipe_right
                                                          ed
                                                          FStar_Syntax_Util.get_bind_vc_combinator
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____16194
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____16193
                                                      FStar_Syntax_Subst.compress
                                                     in
                                                  uu____16190.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____16189 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (uu____16235::uu____16236::bs,uu____16238)
                                                    when
                                                    (FStar_List.length bs) >=
                                                      (Prims.of_int (2))
                                                    ->
                                                    let uu____16290 =
                                                      let uu____16299 =
                                                        FStar_All.pipe_right
                                                          bs
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs)
                                                                -
                                                                (Prims.of_int (2))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____16299
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____16290
                                                      (FStar_List.map
                                                         (fun uu____16430  ->
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.unit_const))
                                                | uu____16437 ->
                                                    let uu____16438 =
                                                      let uu____16444 =
                                                        let uu____16446 =
                                                          FStar_Ident.string_of_lid
                                                            ed.FStar_Syntax_Syntax.mname
                                                           in
                                                        let uu____16448 =
                                                          let uu____16450 =
                                                            let uu____16451 =
                                                              FStar_All.pipe_right
                                                                ed
                                                                FStar_Syntax_Util.get_bind_vc_combinator
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____16451
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____16450
                                                            FStar_Syntax_Print.term_to_string
                                                           in
                                                        FStar_Util.format2
                                                          "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                          uu____16446
                                                          uu____16448
                                                         in
                                                      (FStar_Errors.Fatal_UnexpectedEffect,
                                                        uu____16444)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____16438 rng
                                                 in
                                              let uu____16485 =
                                                FStar_Syntax_Syntax.as_arg
                                                  lb.FStar_Syntax_Syntax.lbtyp
                                                 in
                                              let uu____16494 =
                                                let uu____16505 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____16514 =
                                                  let uu____16525 =
                                                    let uu____16536 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head4
                                                       in
                                                    let uu____16545 =
                                                      let uu____16556 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          body2
                                                         in
                                                      [uu____16556]  in
                                                    uu____16536 ::
                                                      uu____16545
                                                     in
                                                  FStar_List.append unit_args
                                                    uu____16525
                                                   in
                                                uu____16505 :: uu____16514
                                                 in
                                              uu____16485 :: uu____16494
                                            else
                                              (let uu____16615 =
                                                 let uu____16626 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____16635 =
                                                   let uu____16646 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   [uu____16646]  in
                                                 uu____16626 :: uu____16635
                                                  in
                                               let uu____16679 =
                                                 let uu____16690 =
                                                   let uu____16701 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       FStar_Syntax_Syntax.tun
                                                      in
                                                   let uu____16710 =
                                                     let uu____16721 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         head4
                                                        in
                                                     let uu____16730 =
                                                       let uu____16741 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let uu____16750 =
                                                         let uu____16761 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2
                                                            in
                                                         [uu____16761]  in
                                                       uu____16741 ::
                                                         uu____16750
                                                        in
                                                     uu____16721 ::
                                                       uu____16730
                                                      in
                                                   uu____16701 :: uu____16710
                                                    in
                                                 FStar_List.append
                                                   maybe_range_arg
                                                   uu____16690
                                                  in
                                               FStar_List.append uu____16615
                                                 uu____16679)
                                             in
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (bind_inst, args))
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____16842  ->
                                             let uu____16843 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____16845 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____16843 uu____16845);
                                        (let uu____16848 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____16848 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____16876 = FStar_Options.defensive ()  in
                        if uu____16876
                        then
                          let is_arg_impure uu____16891 =
                            match uu____16891 with
                            | (e,q) ->
                                let uu____16905 =
                                  let uu____16906 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____16906.FStar_Syntax_Syntax.n  in
                                (match uu____16905 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____16922 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____16922
                                 | uu____16924 -> false)
                             in
                          let uu____16926 =
                            let uu____16928 =
                              let uu____16939 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____16939 :: args  in
                            FStar_Util.for_some is_arg_impure uu____16928  in
                          (if uu____16926
                           then
                             let uu____16965 =
                               let uu____16971 =
                                 let uu____16973 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____16973
                                  in
                               (FStar_Errors.Warning_Defensive, uu____16971)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____16965
                           else ())
                        else ());
                       (let fallback1 uu____16986 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____16990  ->
                               let uu____16991 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____16991 "");
                          (let uu____16995 = FStar_List.tl stack  in
                           let uu____16996 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____16995 uu____16996)
                           in
                        let fallback2 uu____17002 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____17006  ->
                               let uu____17007 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____17007 "");
                          (let uu____17011 = FStar_List.tl stack  in
                           let uu____17012 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____17011 uu____17012)
                           in
                        let uu____17017 =
                          let uu____17018 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____17018.FStar_Syntax_Syntax.n  in
                        match uu____17017 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____17024 =
                              let uu____17026 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____17026  in
                            if uu____17024
                            then fallback1 ()
                            else
                              (let uu____17031 =
                                 let uu____17033 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____17033  in
                               if uu____17031
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____17050 =
                                      let uu____17055 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____17055 args
                                       in
                                    uu____17050 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____17056 = FStar_List.tl stack  in
                                  norm cfg env uu____17056 t1))
                        | uu____17057 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____17059) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____17083 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____17083  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____17087  ->
                            let uu____17088 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____17088);
                       (let uu____17091 = FStar_List.tl stack  in
                        norm cfg env uu____17091 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____17212  ->
                                match uu____17212 with
                                | (pat,wopt,tm) ->
                                    let uu____17260 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____17260)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____17292 = FStar_List.tl stack  in
                      norm cfg env uu____17292 tm
                  | uu____17293 -> fallback ()))

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
              (fun uu____17307  ->
                 let uu____17308 = FStar_Ident.string_of_lid msrc  in
                 let uu____17310 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17312 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17308
                   uu____17310 uu____17312);
            (let uu____17315 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____17318 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env)
                     in
                  Prims.op_Negation uu____17318)
                in
             if uu____17315
             then
               let ed =
                 let uu____17323 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17323  in
               let uu____17324 =
                 let uu____17331 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr
                    in
                 FStar_All.pipe_right uu____17331 FStar_Util.must  in
               match uu____17324 with
               | (uu____17368,return_repr) ->
                   let return_inst =
                     let uu____17377 =
                       let uu____17378 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17378.FStar_Syntax_Syntax.n  in
                     match uu____17377 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17384::[]) ->
                         let uu____17389 =
                           let uu____17396 =
                             let uu____17397 =
                               let uu____17404 =
                                 let uu____17405 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17405]  in
                               (return_tm, uu____17404)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17397  in
                           FStar_Syntax_Syntax.mk uu____17396  in
                         uu____17389 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17408 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17412 =
                     let uu____17419 =
                       let uu____17420 =
                         let uu____17437 =
                           let uu____17448 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17457 =
                             let uu____17468 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17468]  in
                           uu____17448 :: uu____17457  in
                         (return_inst, uu____17437)  in
                       FStar_Syntax_Syntax.Tm_app uu____17420  in
                     FStar_Syntax_Syntax.mk uu____17419  in
                   uu____17412 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17515 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17515 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17518 =
                      let uu____17520 = FStar_Ident.text_of_lid msrc  in
                      let uu____17522 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17520 uu____17522
                       in
                    failwith uu____17518
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17525;
                      FStar_TypeChecker_Env.mtarget = uu____17526;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17527;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17547 =
                      let uu____17549 = FStar_Ident.text_of_lid msrc  in
                      let uu____17551 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17549 uu____17551
                       in
                    failwith uu____17547
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17554;
                      FStar_TypeChecker_Env.mtarget = uu____17555;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17556;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____17587 =
                        FStar_TypeChecker_Env.is_reifiable_effect env msrc
                         in
                      if uu____17587
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____17592 =
                           let uu____17599 =
                             let uu____17600 =
                               let uu____17619 =
                                 let uu____17628 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____17628]  in
                               (uu____17619, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____17600  in
                           FStar_Syntax_Syntax.mk uu____17599  in
                         uu____17592 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____17661 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    lift uu____17661 t e1))

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
                (fun uu____17731  ->
                   match uu____17731 with
                   | (a,imp) ->
                       let uu____17750 = norm cfg env [] a  in
                       (uu____17750, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17760  ->
             let uu____17761 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17763 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17761 uu____17763);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17789 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17792  -> FStar_Pervasives_Native.Some _17792)
                     uu____17789
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2211_17793 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2211_17793.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2211_17793.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17815 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17818  -> FStar_Pervasives_Native.Some _17818)
                     uu____17815
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2222_17819 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2222_17819.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2222_17819.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17864  ->
                      match uu____17864 with
                      | (a,i) ->
                          let uu____17884 = norm cfg env [] a  in
                          (uu____17884, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17906  ->
                       match uu___14_17906 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17910 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17910
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2239_17918 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2241_17921 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2241_17921.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2239_17918.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2239_17918.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____17925 = b  in
        match uu____17925 with
        | (x,imp) ->
            let x1 =
              let uu___2249_17933 = x  in
              let uu____17934 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2249_17933.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2249_17933.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17934
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____17945 =
                    let uu____17946 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____17946  in
                  FStar_Pervasives_Native.Some uu____17945
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17957 =
          FStar_List.fold_left
            (fun uu____17991  ->
               fun b  ->
                 match uu____17991 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17957 with | (nbs,uu____18071) -> FStar_List.rev nbs

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
            let uu____18103 =
              let uu___2274_18104 = rc  in
              let uu____18105 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2274_18104.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____18105;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2274_18104.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____18103
        | uu____18123 -> lopt

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
            (let uu____18133 = FStar_Syntax_Print.term_to_string tm  in
             let uu____18135 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____18133 uu____18135)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_18147  ->
      match uu___15_18147 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____18160 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____18160 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____18164 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____18164)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____18172 = norm_cb cfg  in
            reduce_primops uu____18172 cfg env tm  in
          let uu____18177 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____18177
          then tm1
          else
            (let w t =
               let uu___2303_18196 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2303_18196.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2303_18196.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____18208 =
                 let uu____18209 = FStar_Syntax_Util.unmeta t  in
                 uu____18209.FStar_Syntax_Syntax.n  in
               match uu____18208 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____18221 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18285)::args1,(bv,uu____18288)::bs1) ->
                   let uu____18342 =
                     let uu____18343 = FStar_Syntax_Subst.compress t  in
                     uu____18343.FStar_Syntax_Syntax.n  in
                   (match uu____18342 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18348 -> false)
               | ([],[]) -> true
               | (uu____18379,uu____18380) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18431 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18433 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18431
                    uu____18433)
               else ();
               (let uu____18438 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18438 with
                | (hd1,args) ->
                    let uu____18477 =
                      let uu____18478 = FStar_Syntax_Subst.compress hd1  in
                      uu____18478.FStar_Syntax_Syntax.n  in
                    (match uu____18477 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____18486 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18488 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18490 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18486 uu____18488 uu____18490)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18495 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18513 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18515 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18513
                    uu____18515)
               else ();
               (let uu____18520 = FStar_Syntax_Util.is_squash t  in
                match uu____18520 with
                | FStar_Pervasives_Native.Some (uu____18531,t') ->
                    is_applied bs t'
                | uu____18543 ->
                    let uu____18552 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18552 with
                     | FStar_Pervasives_Native.Some (uu____18563,t') ->
                         is_applied bs t'
                     | uu____18575 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18599 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18599 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18606)::(q,uu____18608)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18651 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18653 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18651 uu____18653)
                    else ();
                    (let uu____18658 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18658 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18663 =
                           let uu____18664 = FStar_Syntax_Subst.compress p
                              in
                           uu____18664.FStar_Syntax_Syntax.n  in
                         (match uu____18663 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18675 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18675))
                          | uu____18678 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18681)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18706 =
                           let uu____18707 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18707.FStar_Syntax_Syntax.n  in
                         (match uu____18706 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18718 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18718))
                          | uu____18721 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18725 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18725 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18730 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18730 with
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
                                     let uu____18744 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18744))
                               | uu____18747 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18752)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18777 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18777 with
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
                                     let uu____18791 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18791))
                               | uu____18794 -> FStar_Pervasives_Native.None)
                          | uu____18797 -> FStar_Pervasives_Native.None)
                     | uu____18800 -> FStar_Pervasives_Native.None))
               | uu____18803 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18816 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18816 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18822)::[],uu____18823,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18843 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18845 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18843
                         uu____18845)
                    else ();
                    is_quantified_const bv phi')
               | uu____18850 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18865 =
                 let uu____18866 = FStar_Syntax_Subst.compress phi  in
                 uu____18866.FStar_Syntax_Syntax.n  in
               match uu____18865 with
               | FStar_Syntax_Syntax.Tm_match (uu____18872,br::brs) ->
                   let uu____18939 = br  in
                   (match uu____18939 with
                    | (uu____18957,uu____18958,e) ->
                        let r =
                          let uu____18980 = simp_t e  in
                          match uu____18980 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18992 =
                                FStar_List.for_all
                                  (fun uu____19011  ->
                                     match uu____19011 with
                                     | (uu____19025,uu____19026,e') ->
                                         let uu____19040 = simp_t e'  in
                                         uu____19040 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18992
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____19056 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____19066 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____19066
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____19104 =
                 match uu____19104 with
                 | (t1,q) ->
                     let uu____19125 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____19125 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____19157 -> (t1, q))
                  in
               let uu____19170 = FStar_Syntax_Util.head_and_args t  in
               match uu____19170 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____19250 =
                 let uu____19251 = FStar_Syntax_Util.unmeta ty  in
                 uu____19251.FStar_Syntax_Syntax.n  in
               match uu____19250 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____19256) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____19261,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____19285 -> false  in
             let simplify1 arg =
               let uu____19318 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____19318, arg)  in
             let uu____19333 = is_forall_const tm1  in
             match uu____19333 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____19339 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____19341 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____19339
                       uu____19341)
                  else ();
                  (let uu____19346 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____19346))
             | FStar_Pervasives_Native.None  ->
                 let uu____19347 =
                   let uu____19348 = FStar_Syntax_Subst.compress tm1  in
                   uu____19348.FStar_Syntax_Syntax.n  in
                 (match uu____19347 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19352;
                              FStar_Syntax_Syntax.vars = uu____19353;_},uu____19354);
                         FStar_Syntax_Syntax.pos = uu____19355;
                         FStar_Syntax_Syntax.vars = uu____19356;_},args)
                      ->
                      let uu____19386 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19386
                      then
                        let uu____19389 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19389 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19447)::
                             (uu____19448,(arg,uu____19450))::[] ->
                             maybe_auto_squash arg
                         | (uu____19523,(arg,uu____19525))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19526)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19599)::uu____19600::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19670::(FStar_Pervasives_Native.Some (false
                                         ),uu____19671)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19741 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19759 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19759
                         then
                           let uu____19762 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19762 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19820)::uu____19821::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19891::(FStar_Pervasives_Native.Some (true
                                           ),uu____19892)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19962)::(uu____19963,(arg,uu____19965))::[]
                               -> maybe_auto_squash arg
                           | (uu____20038,(arg,uu____20040))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20041)::[]
                               -> maybe_auto_squash arg
                           | uu____20114 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20132 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20132
                            then
                              let uu____20135 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20135 with
                              | uu____20193::(FStar_Pervasives_Native.Some
                                              (true ),uu____20194)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20264)::uu____20265::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20335)::(uu____20336,(arg,uu____20338))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20411,(p,uu____20413))::(uu____20414,
                                                                (q,uu____20416))::[]
                                  ->
                                  let uu____20488 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20488
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20493 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20511 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20511
                               then
                                 let uu____20514 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20514 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20572)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20573)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20647)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20648)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20722)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20723)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20797)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20798)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20872,(arg,uu____20874))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20875)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20948)::(uu____20949,(arg,uu____20951))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21024,(arg,uu____21026))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21027)::[]
                                     ->
                                     let uu____21100 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21100
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21101)::(uu____21102,(arg,uu____21104))::[]
                                     ->
                                     let uu____21177 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21177
                                 | (uu____21178,(p,uu____21180))::(uu____21181,
                                                                   (q,uu____21183))::[]
                                     ->
                                     let uu____21255 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21255
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21260 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21278 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21278
                                  then
                                    let uu____21281 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21281 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21339)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21383)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21427 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21445 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21445
                                     then
                                       match args with
                                       | (t,uu____21449)::[] ->
                                           let uu____21474 =
                                             let uu____21475 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21475.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21474 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21478::[],body,uu____21480)
                                                ->
                                                let uu____21515 = simp_t body
                                                   in
                                                (match uu____21515 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21521 -> tm1)
                                            | uu____21525 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21527))::(t,uu____21529)::[]
                                           ->
                                           let uu____21569 =
                                             let uu____21570 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21570.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21569 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21573::[],body,uu____21575)
                                                ->
                                                let uu____21610 = simp_t body
                                                   in
                                                (match uu____21610 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21618 -> tm1)
                                            | uu____21622 -> tm1)
                                       | uu____21623 -> tm1
                                     else
                                       (let uu____21636 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21636
                                        then
                                          match args with
                                          | (t,uu____21640)::[] ->
                                              let uu____21665 =
                                                let uu____21666 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21666.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21665 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21669::[],body,uu____21671)
                                                   ->
                                                   let uu____21706 =
                                                     simp_t body  in
                                                   (match uu____21706 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21712 -> tm1)
                                               | uu____21716 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21718))::(t,uu____21720)::[]
                                              ->
                                              let uu____21760 =
                                                let uu____21761 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21761.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21760 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21764::[],body,uu____21766)
                                                   ->
                                                   let uu____21801 =
                                                     simp_t body  in
                                                   (match uu____21801 with
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
                                                    | uu____21809 -> tm1)
                                               | uu____21813 -> tm1)
                                          | uu____21814 -> tm1
                                        else
                                          (let uu____21827 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21827
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21830;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21831;_},uu____21832)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21858;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21859;_},uu____21860)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21886 -> tm1
                                           else
                                             (let uu____21899 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____21899
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____21913 =
                                                    let uu____21914 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____21914.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____21913 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21925 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21939 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____21939
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____21978 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____21978
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21984 =
                                                         let uu____21985 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____21985.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____21984 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21988 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____21996 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____21996
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____22005
                                                                  =
                                                                  let uu____22006
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____22006.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____22005
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____22012)
                                                                    -> hd1
                                                                | uu____22037
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____22041
                                                                =
                                                                let uu____22052
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____22052]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____22041)
                                                       | uu____22085 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____22090 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____22090 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____22110 ->
                                                     let uu____22119 =
                                                       let uu____22126 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____22126 cfg env
                                                        in
                                                     uu____22119 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____22132;
                         FStar_Syntax_Syntax.vars = uu____22133;_},args)
                      ->
                      let uu____22159 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22159
                      then
                        let uu____22162 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22162 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22220)::
                             (uu____22221,(arg,uu____22223))::[] ->
                             maybe_auto_squash arg
                         | (uu____22296,(arg,uu____22298))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22299)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22372)::uu____22373::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22443::(FStar_Pervasives_Native.Some (false
                                         ),uu____22444)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22514 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22532 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22532
                         then
                           let uu____22535 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22535 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22593)::uu____22594::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22664::(FStar_Pervasives_Native.Some (true
                                           ),uu____22665)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22735)::(uu____22736,(arg,uu____22738))::[]
                               -> maybe_auto_squash arg
                           | (uu____22811,(arg,uu____22813))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22814)::[]
                               -> maybe_auto_squash arg
                           | uu____22887 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22905 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22905
                            then
                              let uu____22908 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____22908 with
                              | uu____22966::(FStar_Pervasives_Native.Some
                                              (true ),uu____22967)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____23037)::uu____23038::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____23108)::(uu____23109,(arg,uu____23111))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23184,(p,uu____23186))::(uu____23187,
                                                                (q,uu____23189))::[]
                                  ->
                                  let uu____23261 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23261
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23266 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23284 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23284
                               then
                                 let uu____23287 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23287 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23345)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23346)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23420)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23421)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23495)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23496)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23570)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23571)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23645,(arg,uu____23647))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23648)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23721)::(uu____23722,(arg,uu____23724))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23797,(arg,uu____23799))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23800)::[]
                                     ->
                                     let uu____23873 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23873
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23874)::(uu____23875,(arg,uu____23877))::[]
                                     ->
                                     let uu____23950 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23950
                                 | (uu____23951,(p,uu____23953))::(uu____23954,
                                                                   (q,uu____23956))::[]
                                     ->
                                     let uu____24028 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____24028
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____24033 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____24051 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____24051
                                  then
                                    let uu____24054 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____24054 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____24112)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____24156)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____24200 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____24218 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____24218
                                     then
                                       match args with
                                       | (t,uu____24222)::[] ->
                                           let uu____24247 =
                                             let uu____24248 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24248.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24247 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24251::[],body,uu____24253)
                                                ->
                                                let uu____24288 = simp_t body
                                                   in
                                                (match uu____24288 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24294 -> tm1)
                                            | uu____24298 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24300))::(t,uu____24302)::[]
                                           ->
                                           let uu____24342 =
                                             let uu____24343 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24343.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24342 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24346::[],body,uu____24348)
                                                ->
                                                let uu____24383 = simp_t body
                                                   in
                                                (match uu____24383 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24391 -> tm1)
                                            | uu____24395 -> tm1)
                                       | uu____24396 -> tm1
                                     else
                                       (let uu____24409 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24409
                                        then
                                          match args with
                                          | (t,uu____24413)::[] ->
                                              let uu____24438 =
                                                let uu____24439 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24439.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24438 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24442::[],body,uu____24444)
                                                   ->
                                                   let uu____24479 =
                                                     simp_t body  in
                                                   (match uu____24479 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24485 -> tm1)
                                               | uu____24489 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24491))::(t,uu____24493)::[]
                                              ->
                                              let uu____24533 =
                                                let uu____24534 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24534.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24533 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24537::[],body,uu____24539)
                                                   ->
                                                   let uu____24574 =
                                                     simp_t body  in
                                                   (match uu____24574 with
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
                                                    | uu____24582 -> tm1)
                                               | uu____24586 -> tm1)
                                          | uu____24587 -> tm1
                                        else
                                          (let uu____24600 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24600
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24603;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24604;_},uu____24605)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24631;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24632;_},uu____24633)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24659 -> tm1
                                           else
                                             (let uu____24672 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____24672
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____24686 =
                                                    let uu____24687 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____24687.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____24686 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____24698 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24712 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____24712
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____24747 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____24747
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24753 =
                                                         let uu____24754 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____24754.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____24753 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24757 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24765 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24765
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24774
                                                                  =
                                                                  let uu____24775
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24775.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24774
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____24781)
                                                                    -> hd1
                                                                | uu____24806
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____24810
                                                                =
                                                                let uu____24821
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____24821]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24810)
                                                       | uu____24854 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24859 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____24859 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24879 ->
                                                     let uu____24888 =
                                                       let uu____24895 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____24895 cfg env
                                                        in
                                                     uu____24888 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24906 = simp_t t  in
                      (match uu____24906 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24915 ->
                      let uu____24938 = is_const_match tm1  in
                      (match uu____24938 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24947 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____24957  ->
               (let uu____24959 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24961 = FStar_Syntax_Print.term_to_string t  in
                let uu____24963 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24971 =
                  let uu____24973 =
                    let uu____24976 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24976
                     in
                  stack_to_string uu____24973  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24959 uu____24961 uu____24963 uu____24971);
               (let uu____25001 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____25001
                then
                  let uu____25005 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____25005 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____25012 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____25014 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____25016 =
                          let uu____25018 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____25018
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____25012
                          uu____25014 uu____25016);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____25040 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____25048)::uu____25049 -> true
                | uu____25059 -> false)
              in
           if uu____25040
           then
             let uu____25062 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____25062 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____25076 =
                        let uu____25078 =
                          let uu____25080 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____25080  in
                        FStar_Util.string_of_int uu____25078  in
                      let uu____25087 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____25089 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                      let uu____25091 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____25076 uu____25087 uu____25089 uu____25091)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____25100,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____25129  ->
                        let uu____25130 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____25130);
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
                  let uu____25173 =
                    let uu___2932_25174 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2932_25174.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2932_25174.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____25173
              | (Arg (Univ uu____25177,uu____25178,uu____25179))::uu____25180
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____25184,uu____25185))::uu____25186 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____25202,uu____25203),aq,r))::stack1
                  when
                  let uu____25255 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____25255 ->
                  let t2 =
                    let uu____25259 =
                      let uu____25264 =
                        let uu____25265 = closure_as_term cfg env_arg tm  in
                        (uu____25265, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____25264  in
                    uu____25259 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____25275),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____25330  ->
                        let uu____25331 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____25331);
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
                     (let uu____25351 = FStar_ST.op_Bang m  in
                      match uu____25351 with
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
                      | FStar_Pervasives_Native.Some (uu____25439,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____25495 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____25500  ->
                         let uu____25501 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____25501);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____25511 =
                    let uu____25512 = FStar_Syntax_Subst.compress t1  in
                    uu____25512.FStar_Syntax_Syntax.n  in
                  (match uu____25511 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____25540 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____25540  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____25544  ->
                             let uu____25545 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____25545);
                        (let uu____25548 = FStar_List.tl stack  in
                         norm cfg env1 uu____25548 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____25549);
                          FStar_Syntax_Syntax.pos = uu____25550;
                          FStar_Syntax_Syntax.vars = uu____25551;_},(e,uu____25553)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____25592 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____25609 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____25609 with
                        | (hd1,args) ->
                            let uu____25652 =
                              let uu____25653 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____25653.FStar_Syntax_Syntax.n  in
                            (match uu____25652 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____25657 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____25657 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____25660;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____25661;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____25662;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____25664;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____25665;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____25666;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____25667;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____25703 -> fallback " (3)" ())
                             | uu____25707 -> fallback " (4)" ()))
                   | uu____25709 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____25735  ->
                        let uu____25736 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____25736);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____25747 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25752  ->
                           let uu____25753 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____25755 =
                             let uu____25757 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____25787  ->
                                       match uu____25787 with
                                       | (p,uu____25798,uu____25799) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____25757
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____25753 uu____25755);
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
                                (fun uu___16_25821  ->
                                   match uu___16_25821 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____25825 -> false))
                            in
                         let steps =
                           let uu___3100_25828 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___3100_25828.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___3103_25835 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___3103_25835.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___3103_25835.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___3103_25835.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___3103_25835.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___3103_25835.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___3103_25835.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____25910 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____25941 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____26030  ->
                                       fun uu____26031  ->
                                         match (uu____26030, uu____26031)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____26181 =
                                               norm_pat env3 p1  in
                                             (match uu____26181 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____25941 with
                              | (pats1,env3) ->
                                  ((let uu___3131_26351 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___3131_26351.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3135_26372 = x  in
                               let uu____26373 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3135_26372.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3135_26372.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26373
                               }  in
                             ((let uu___3138_26387 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3138_26387.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3142_26398 = x  in
                               let uu____26399 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3142_26398.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3142_26398.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26399
                               }  in
                             ((let uu___3145_26413 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3145_26413.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3151_26429 = x  in
                               let uu____26430 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3151_26429.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3151_26429.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____26430
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3155_26445 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3155_26445.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____26489 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____26519 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____26519 with
                                     | (p,wopt,e) ->
                                         let uu____26539 = norm_pat env1 p
                                            in
                                         (match uu____26539 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____26594 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____26594
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____26611 =
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
                         if uu____26611
                         then
                           norm
                             (let uu___3174_26618 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3176_26621 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3176_26621.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3174_26618.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3174_26618.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3174_26618.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3174_26618.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3174_26618.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3174_26618.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3174_26618.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3174_26618.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____26625 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____26625)
                       in
                    let rec is_cons head1 =
                      let uu____26651 =
                        let uu____26652 = FStar_Syntax_Subst.compress head1
                           in
                        uu____26652.FStar_Syntax_Syntax.n  in
                      match uu____26651 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____26657) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____26662 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26664;
                            FStar_Syntax_Syntax.fv_delta = uu____26665;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____26667;
                            FStar_Syntax_Syntax.fv_delta = uu____26668;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____26669);_}
                          -> true
                      | uu____26677 -> false  in
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
                      let uu____26846 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____26846 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____26943 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26985 ->
                                    let uu____26986 =
                                      let uu____26988 = is_cons head1  in
                                      Prims.op_Negation uu____26988  in
                                    FStar_Util.Inr uu____26986)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____27017 =
                                 let uu____27018 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____27018.FStar_Syntax_Syntax.n  in
                               (match uu____27017 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____27037 ->
                                    let uu____27038 =
                                      let uu____27040 = is_cons head1  in
                                      Prims.op_Negation uu____27040  in
                                    FStar_Util.Inr uu____27038))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____27131)::rest_a,(p1,uu____27134)::rest_p)
                          ->
                          let uu____27193 = matches_pat t2 p1  in
                          (match uu____27193 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____27246 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____27369 = matches_pat scrutinee1 p1  in
                          (match uu____27369 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____27415  ->
                                     let uu____27416 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____27418 =
                                       let uu____27420 =
                                         FStar_List.map
                                           (fun uu____27432  ->
                                              match uu____27432 with
                                              | (uu____27438,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____27420
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____27416 uu____27418);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____27474  ->
                                          match uu____27474 with
                                          | (bv,t2) ->
                                              let uu____27497 =
                                                let uu____27504 =
                                                  let uu____27507 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____27507
                                                   in
                                                let uu____27508 =
                                                  let uu____27509 =
                                                    let uu____27541 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____27541,
                                                      false)
                                                     in
                                                  Clos uu____27509  in
                                                (uu____27504, uu____27508)
                                                 in
                                              uu____27497 :: env2) env1 s
                                    in
                                 let uu____27634 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____27634)))
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
            (fun uu____27667  ->
               let uu____27668 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____27668);
          (let uu____27671 = is_nbe_request s  in
           if uu____27671
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27677  ->
                   let uu____27678 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27678);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27684  ->
                   let uu____27685 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27685);
              (let uu____27688 =
                 FStar_Util.record_time (fun uu____27695  -> nbe_eval c s t)
                  in
               match uu____27688 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27704  ->
                         let uu____27705 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27707 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27705 uu____27707);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27715  ->
                   let uu____27716 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27716);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27722  ->
                   let uu____27723 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27723);
              (let uu____27726 =
                 FStar_Util.record_time (fun uu____27733  -> norm c [] [] t)
                  in
               match uu____27726 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27748  ->
                         let uu____27749 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27751 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27749 uu____27751);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27770 =
          let uu____27774 =
            let uu____27776 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____27776  in
          FStar_Pervasives_Native.Some uu____27774  in
        FStar_Profiling.profile
          (fun uu____27779  -> normalize_with_primitive_steps [] s e t)
          uu____27770 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____27801  ->
             let uu____27802 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____27802);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____27808  ->
             let uu____27809 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____27809);
        (let uu____27812 =
           FStar_Util.record_time (fun uu____27819  -> norm_comp cfg [] c)
            in
         match uu____27812 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____27834  ->
                   let uu____27835 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____27837 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____27835
                     uu____27837);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27851 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____27851 [] u
  
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
      let uu____27873 = normalize steps env t  in
      FStar_TypeChecker_Env.non_informative env uu____27873
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27885 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env t ->
          let uu___3344_27904 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3344_27904.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3344_27904.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27911 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27911
          then
            let ct1 =
              let uu____27915 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27915 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____27922 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27922
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3354_27929 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3354_27929.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3354_27929.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3354_27929.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c
                     in
                  let uu___3358_27931 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3358_27931.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3358_27931.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3358_27931.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3358_27931.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3361_27932 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3361_27932.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3361_27932.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27935 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      let uu____27947 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____27947
      then
        let uu____27950 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____27950 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3369_27954 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3369_27954.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3369_27954.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3369_27954.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3376_27973  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3375_27976 ->
            ((let uu____27978 =
                let uu____27984 =
                  let uu____27986 = FStar_Util.message_of_exn uu___3375_27976
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27986
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27984)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27978);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3386_28005  ->
             match () with
             | () ->
                 let uu____28006 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____28006 [] c) ()
        with
        | uu___3385_28015 ->
            ((let uu____28017 =
                let uu____28023 =
                  let uu____28025 = FStar_Util.message_of_exn uu___3385_28015
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____28025
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____28023)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____28017);
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
                   let uu____28074 =
                     let uu____28075 =
                       let uu____28082 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____28082)  in
                     FStar_Syntax_Syntax.Tm_refine uu____28075  in
                   mk uu____28074 t01.FStar_Syntax_Syntax.pos
               | uu____28087 -> t2)
          | uu____28088 -> t2  in
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
        let uu____28182 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____28182 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____28219 ->
                 let uu____28228 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____28228 with
                  | (actuals,uu____28238,uu____28239) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____28259 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____28259 with
                         | (binders,args) ->
                             let uu____28270 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____28270
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
      | uu____28285 ->
          let uu____28286 = FStar_Syntax_Util.head_and_args t  in
          (match uu____28286 with
           | (head1,args) ->
               let uu____28329 =
                 let uu____28330 = FStar_Syntax_Subst.compress head1  in
                 uu____28330.FStar_Syntax_Syntax.n  in
               (match uu____28329 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____28351 =
                      let uu____28366 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____28366  in
                    (match uu____28351 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____28406 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3456_28414 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3456_28414.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3456_28414.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3456_28414.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3456_28414.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3456_28414.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3456_28414.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3456_28414.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3456_28414.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3456_28414.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3456_28414.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3456_28414.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3456_28414.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3456_28414.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3456_28414.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3456_28414.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3456_28414.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3456_28414.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3456_28414.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3456_28414.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3456_28414.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3456_28414.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3456_28414.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3456_28414.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3456_28414.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3456_28414.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3456_28414.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3456_28414.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3456_28414.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3456_28414.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3456_28414.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3456_28414.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3456_28414.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3456_28414.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3456_28414.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3456_28414.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3456_28414.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3456_28414.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3456_28414.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3456_28414.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3456_28414.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3456_28414.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3456_28414.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3456_28414.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____28406 with
                            | (uu____28417,ty,uu____28419) ->
                                eta_expand_with_type env t ty))
                | uu____28420 ->
                    let uu____28421 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3463_28429 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3463_28429.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3463_28429.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3463_28429.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3463_28429.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3463_28429.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3463_28429.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3463_28429.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3463_28429.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3463_28429.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3463_28429.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3463_28429.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3463_28429.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3463_28429.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3463_28429.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3463_28429.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3463_28429.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3463_28429.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3463_28429.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3463_28429.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3463_28429.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3463_28429.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3463_28429.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3463_28429.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3463_28429.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3463_28429.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3463_28429.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3463_28429.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3463_28429.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3463_28429.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3463_28429.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3463_28429.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3463_28429.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3463_28429.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3463_28429.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3463_28429.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3463_28429.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3463_28429.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3463_28429.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3463_28429.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3463_28429.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3463_28429.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3463_28429.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3463_28429.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____28421 with
                     | (uu____28432,ty,uu____28434) ->
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
      let uu___3475_28516 = x  in
      let uu____28517 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3475_28516.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3475_28516.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28517
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28520 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28544 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28545 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28546 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28547 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28554 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28555 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28556 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3501_28590 = rc  in
          let uu____28591 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28600 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3501_28590.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28591;
            FStar_Syntax_Syntax.residual_flags = uu____28600
          }  in
        let uu____28603 =
          let uu____28604 =
            let uu____28623 = elim_delayed_subst_binders bs  in
            let uu____28632 = elim_delayed_subst_term t2  in
            let uu____28635 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28623, uu____28632, uu____28635)  in
          FStar_Syntax_Syntax.Tm_abs uu____28604  in
        mk1 uu____28603
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28672 =
          let uu____28673 =
            let uu____28688 = elim_delayed_subst_binders bs  in
            let uu____28697 = elim_delayed_subst_comp c  in
            (uu____28688, uu____28697)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28673  in
        mk1 uu____28672
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28716 =
          let uu____28717 =
            let uu____28724 = elim_bv bv  in
            let uu____28725 = elim_delayed_subst_term phi  in
            (uu____28724, uu____28725)  in
          FStar_Syntax_Syntax.Tm_refine uu____28717  in
        mk1 uu____28716
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____28756 =
          let uu____28757 =
            let uu____28774 = elim_delayed_subst_term t2  in
            let uu____28777 = elim_delayed_subst_args args  in
            (uu____28774, uu____28777)  in
          FStar_Syntax_Syntax.Tm_app uu____28757  in
        mk1 uu____28756
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3523_28849 = p  in
              let uu____28850 =
                let uu____28851 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28851  in
              {
                FStar_Syntax_Syntax.v = uu____28850;
                FStar_Syntax_Syntax.p =
                  (uu___3523_28849.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3527_28853 = p  in
              let uu____28854 =
                let uu____28855 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28855  in
              {
                FStar_Syntax_Syntax.v = uu____28854;
                FStar_Syntax_Syntax.p =
                  (uu___3527_28853.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3533_28862 = p  in
              let uu____28863 =
                let uu____28864 =
                  let uu____28871 = elim_bv x  in
                  let uu____28872 = elim_delayed_subst_term t0  in
                  (uu____28871, uu____28872)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28864  in
              {
                FStar_Syntax_Syntax.v = uu____28863;
                FStar_Syntax_Syntax.p =
                  (uu___3533_28862.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3539_28897 = p  in
              let uu____28898 =
                let uu____28899 =
                  let uu____28913 =
                    FStar_List.map
                      (fun uu____28939  ->
                         match uu____28939 with
                         | (x,b) ->
                             let uu____28956 = elim_pat x  in
                             (uu____28956, b)) pats
                     in
                  (fv, uu____28913)  in
                FStar_Syntax_Syntax.Pat_cons uu____28899  in
              {
                FStar_Syntax_Syntax.v = uu____28898;
                FStar_Syntax_Syntax.p =
                  (uu___3539_28897.FStar_Syntax_Syntax.p)
              }
          | uu____28971 -> p  in
        let elim_branch uu____28995 =
          match uu____28995 with
          | (pat,wopt,t3) ->
              let uu____29021 = elim_pat pat  in
              let uu____29024 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____29027 = elim_delayed_subst_term t3  in
              (uu____29021, uu____29024, uu____29027)
           in
        let uu____29032 =
          let uu____29033 =
            let uu____29056 = elim_delayed_subst_term t2  in
            let uu____29059 = FStar_List.map elim_branch branches  in
            (uu____29056, uu____29059)  in
          FStar_Syntax_Syntax.Tm_match uu____29033  in
        mk1 uu____29032
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____29190 =
          match uu____29190 with
          | (tc,topt) ->
              let uu____29225 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____29235 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____29235
                | FStar_Util.Inr c ->
                    let uu____29237 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____29237
                 in
              let uu____29238 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____29225, uu____29238)
           in
        let uu____29247 =
          let uu____29248 =
            let uu____29275 = elim_delayed_subst_term t2  in
            let uu____29278 = elim_ascription a  in
            (uu____29275, uu____29278, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____29248  in
        mk1 uu____29247
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3569_29341 = lb  in
          let uu____29342 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____29345 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3569_29341.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3569_29341.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____29342;
            FStar_Syntax_Syntax.lbeff =
              (uu___3569_29341.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____29345;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3569_29341.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3569_29341.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____29348 =
          let uu____29349 =
            let uu____29363 =
              let uu____29371 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____29371)  in
            let uu____29383 = elim_delayed_subst_term t2  in
            (uu____29363, uu____29383)  in
          FStar_Syntax_Syntax.Tm_let uu____29349  in
        mk1 uu____29348
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____29428 =
          let uu____29429 =
            let uu____29436 = elim_delayed_subst_term tm  in
            (uu____29436, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____29429  in
        mk1 uu____29428
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29447 =
          let uu____29448 =
            let uu____29455 = elim_delayed_subst_term t2  in
            let uu____29458 = elim_delayed_subst_meta md  in
            (uu____29455, uu____29458)  in
          FStar_Syntax_Syntax.Tm_meta uu____29448  in
        mk1 uu____29447

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29467  ->
         match uu___17_29467 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29471 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29471
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
        let uu____29494 =
          let uu____29495 =
            let uu____29504 = elim_delayed_subst_term t  in
            (uu____29504, uopt)  in
          FStar_Syntax_Syntax.Total uu____29495  in
        mk1 uu____29494
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29521 =
          let uu____29522 =
            let uu____29531 = elim_delayed_subst_term t  in
            (uu____29531, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29522  in
        mk1 uu____29521
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3602_29540 = ct  in
          let uu____29541 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29544 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29555 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3602_29540.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3602_29540.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29541;
            FStar_Syntax_Syntax.effect_args = uu____29544;
            FStar_Syntax_Syntax.flags = uu____29555
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29558  ->
    match uu___18_29558 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____29593 =
          let uu____29614 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____29623 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29614, uu____29623)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29593
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____29678 =
          let uu____29685 = elim_delayed_subst_term t  in (m, uu____29685)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____29678
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____29697 =
          let uu____29706 = elim_delayed_subst_term t  in
          (m1, m2, uu____29706)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29697
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
      (fun uu____29739  ->
         match uu____29739 with
         | (t,q) ->
             let uu____29758 = elim_delayed_subst_term t  in (uu____29758, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____29786  ->
         match uu____29786 with
         | (x,q) ->
             let uu____29805 =
               let uu___3628_29806 = x  in
               let uu____29807 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3628_29806.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3628_29806.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29807
               }  in
             (uu____29805, q)) bs

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
            | (uu____29915,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29947,FStar_Util.Inl t) ->
                let uu____29969 =
                  let uu____29976 =
                    let uu____29977 =
                      let uu____29992 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29992)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29977  in
                  FStar_Syntax_Syntax.mk uu____29976  in
                uu____29969 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____30005 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____30005 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____30037 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____30110 ->
                    let uu____30111 =
                      let uu____30120 =
                        let uu____30121 = FStar_Syntax_Subst.compress t4  in
                        uu____30121.FStar_Syntax_Syntax.n  in
                      (uu____30120, tc)  in
                    (match uu____30111 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____30150) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____30197) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____30242,FStar_Util.Inl uu____30243) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____30274 -> failwith "Impossible")
                 in
              (match uu____30037 with
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
          let uu____30413 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____30413 with
          | (univ_names1,binders1,tc) ->
              let uu____30487 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30487)
  
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
          let uu____30541 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____30541 with
          | (univ_names1,binders1,tc) ->
              let uu____30615 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30615)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____30657 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____30657 with
           | (univ_names1,binders1,typ1) ->
               let uu___3711_30697 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3711_30697.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3711_30697.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3711_30697.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3711_30697.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3711_30697.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3717_30712 = s  in
          let uu____30713 =
            let uu____30714 =
              let uu____30723 = FStar_List.map (elim_uvars env) sigs  in
              (uu____30723, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____30714  in
          {
            FStar_Syntax_Syntax.sigel = uu____30713;
            FStar_Syntax_Syntax.sigrng =
              (uu___3717_30712.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3717_30712.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3717_30712.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3717_30712.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3717_30712.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____30742 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30742 with
           | (univ_names1,uu____30766,typ1) ->
               let uu___3731_30788 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3731_30788.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3731_30788.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3731_30788.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3731_30788.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3731_30788.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____30795 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30795 with
           | (univ_names1,uu____30819,typ1) ->
               let uu___3742_30841 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3742_30841.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3742_30841.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3742_30841.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3742_30841.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3742_30841.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30871 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30871 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____30896 =
                            let uu____30897 =
                              let uu____30898 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____30898  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30897
                             in
                          elim_delayed_subst_term uu____30896  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3758_30901 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3758_30901.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3758_30901.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3758_30901.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3758_30901.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3761_30902 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3761_30902.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3761_30902.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3761_30902.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3761_30902.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3761_30902.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3765_30909 = s  in
          let uu____30910 =
            let uu____30911 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____30911  in
          {
            FStar_Syntax_Syntax.sigel = uu____30910;
            FStar_Syntax_Syntax.sigrng =
              (uu___3765_30909.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3765_30909.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3765_30909.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3765_30909.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3765_30909.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____30915 = elim_uvars_aux_t env us [] t  in
          (match uu____30915 with
           | (us1,uu____30939,t1) ->
               let uu___3776_30961 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3776_30961.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3776_30961.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3776_30961.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3776_30961.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3776_30961.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30963 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____30963 with
           | (univs1,binders,uu____30982) ->
               let uu____31003 =
                 let uu____31008 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____31008 with
                 | (univs_opening,univs2) ->
                     let uu____31031 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____31031)
                  in
               (match uu____31003 with
                | (univs_opening,univs_closing) ->
                    let uu____31034 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____31040 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____31041 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____31040, uu____31041)  in
                    (match uu____31034 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____31067 =
                           match uu____31067 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____31085 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____31085 with
                                | (us1,t1) ->
                                    let uu____31096 =
                                      let uu____31105 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____31110 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____31105, uu____31110)  in
                                    (match uu____31096 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____31133 =
                                           let uu____31142 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____31147 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____31142, uu____31147)  in
                                         (match uu____31133 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____31171 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____31171
                                                 in
                                              let uu____31172 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____31172 with
                                               | (uu____31199,uu____31200,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____31223 =
                                                       let uu____31224 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____31224
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____31223
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____31233 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____31233 with
                           | (uu____31252,uu____31253,t1) -> t1  in
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
                             | uu____31329 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____31356 =
                               let uu____31357 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____31357.FStar_Syntax_Syntax.n  in
                             match uu____31356 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____31416 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31450 =
                               let uu____31451 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31451.FStar_Syntax_Syntax.n  in
                             match uu____31450 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31474) ->
                                 let uu____31499 = destruct_action_body body
                                    in
                                 (match uu____31499 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31548 ->
                                 let uu____31549 = destruct_action_body t  in
                                 (match uu____31549 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31604 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31604 with
                           | (action_univs,t) ->
                               let uu____31613 = destruct_action_typ_templ t
                                  in
                               (match uu____31613 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3860_31660 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3860_31660.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3860_31660.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3863_31662 = ed  in
                           let uu____31663 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____31664 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____31665 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3863_31662.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3863_31662.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31663;
                             FStar_Syntax_Syntax.combinators = uu____31664;
                             FStar_Syntax_Syntax.actions = uu____31665;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3863_31662.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3866_31668 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3866_31668.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3866_31668.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3866_31668.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3866_31668.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3866_31668.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31689 =
            match uu___19_31689 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____31720 = elim_uvars_aux_t env us [] t  in
                (match uu____31720 with
                 | (us1,uu____31752,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3881_31783 = sub_eff  in
            let uu____31784 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____31787 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3881_31783.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3881_31783.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____31784;
              FStar_Syntax_Syntax.lift = uu____31787
            }  in
          let uu___3884_31790 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3884_31790.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3884_31790.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3884_31790.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3884_31790.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3884_31790.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____31800 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____31800 with
           | (univ_names1,binders1,comp1) ->
               let uu___3897_31840 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3897_31840.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3897_31840.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3897_31840.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3897_31840.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3897_31840.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31843 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31844 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n1,p,(us_t,t),(us_ty,ty))
          ->
          let uu____31874 = elim_uvars_aux_t env us_t [] t  in
          (match uu____31874 with
           | (us_t1,uu____31898,t1) ->
               let uu____31920 = elim_uvars_aux_t env us_ty [] ty  in
               (match uu____31920 with
                | (us_ty1,uu____31944,ty1) ->
                    let uu___3922_31966 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n1, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3922_31966.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3922_31966.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3922_31966.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3922_31966.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3922_31966.FStar_Syntax_Syntax.sigopts)
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
        let uu____32017 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____32017 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____32039 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____32039 with
             | (uu____32046,head_def) ->
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
      let uu____32052 = FStar_Syntax_Util.head_and_args t  in
      match uu____32052 with
      | (head1,args) ->
          let uu____32097 =
            let uu____32098 = FStar_Syntax_Subst.compress head1  in
            uu____32098.FStar_Syntax_Syntax.n  in
          (match uu____32097 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____32105;
                  FStar_Syntax_Syntax.vars = uu____32106;_},us)
               -> aux fv us args
           | uu____32112 -> FStar_Pervasives_Native.None)
  