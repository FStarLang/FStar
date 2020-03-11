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
                    is_fv head1 FStar_Parser_Const.pure_weaken_wp_lid ->
                    let uu____9879 =
                      let uu____9880 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_weaken uu____9880
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9883  -> FStar_Pervasives_Native.Some _9883)
                      uu____9879
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_strengthen_wp_lid ->
                    let uu____9910 =
                      let uu____9911 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_strengthen uu____9911
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9914  -> FStar_Pervasives_Native.Some _9914)
                      uu____9910
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_if_then_else_lid ->
                    let uu____9941 =
                      let uu____9942 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_if_then_else
                        uu____9942 args1 r
                       in
                    FStar_All.pipe_left
                      (fun _9945  -> FStar_Pervasives_Native.Some _9945)
                      uu____9941
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_ite_lid ->
                    let uu____9972 =
                      let uu____9973 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_ite uu____9973 args1
                        r
                       in
                    FStar_All.pipe_left
                      (fun _9976  -> FStar_Pervasives_Native.Some _9976)
                      uu____9972
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_close_lid ->
                    let uu____10003 =
                      let uu____10004 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_close uu____10004
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _10007  -> FStar_Pervasives_Native.Some _10007)
                      uu____10003
                | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                    is_fv head1 FStar_Parser_Const.pure_null_lid ->
                    let uu____10034 =
                      let uu____10035 = us_of head1  in
                      mk_app1 FStar_Parser_Const.as_req_null uu____10035
                        args1 r
                       in
                    FStar_All.pipe_left
                      (fun _10038  -> FStar_Pervasives_Native.Some _10038)
                      uu____10034
                | uu____10039 -> FStar_Pervasives_Native.None))
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
               let uu____10090 = args  in
               match uu____10090 with
               | uu____10091::(wp,uu____10093)::[] -> wp
             else
               (let uu____10136 = args  in
                match uu____10136 with
                | uu____10137::(wp,uu____10139)::uu____10140::[] -> wp)
              in
           let uu____10197 =
             let uu____10198 = FStar_Syntax_Subst.compress wp  in
             uu____10198.FStar_Syntax_Syntax.n  in
           match uu____10197 with
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.as_wp ->
               let uu____10229 = args1  in
               (match uu____10229 with
                | uu____10242::uu____10243::(ens,uu____10245)::[] ->
                    FStar_Pervasives_Native.Some ens)
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_return_lid ->
               let uu____10328 =
                 let uu____10329 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_return uu____10329 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10332  -> FStar_Pervasives_Native.Some _10332)
                 uu____10328
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_bind_lid ->
               let uu____10359 =
                 let uu____10360 = us_of head1  in
                 let uu____10361 = FStar_All.pipe_right args1 FStar_List.tl
                    in
                 mk_app1 FStar_Parser_Const.as_ens_bind uu____10360
                   uu____10361 r
                  in
               FStar_All.pipe_left
                 (fun _10382  -> FStar_Pervasives_Native.Some _10382)
                 uu____10359
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_assume_wp_lid ->
               let uu____10409 =
                 let uu____10410 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_assume uu____10410 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10413  -> FStar_Pervasives_Native.Some _10413)
                 uu____10409
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_assert_wp_lid ->
               let uu____10440 =
                 let uu____10441 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_assert uu____10441 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10444  -> FStar_Pervasives_Native.Some _10444)
                 uu____10440
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_weaken_wp_lid ->
               let uu____10471 =
                 let uu____10472 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_weaken uu____10472 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10475  -> FStar_Pervasives_Native.Some _10475)
                 uu____10471
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_strengthen_wp_lid ->
               let uu____10502 =
                 let uu____10503 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_strengthen uu____10503
                   args1 r
                  in
               FStar_All.pipe_left
                 (fun _10506  -> FStar_Pervasives_Native.Some _10506)
                 uu____10502
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_if_then_else_lid ->
               let uu____10533 =
                 let uu____10534 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_if_then_else uu____10534
                   args1 r
                  in
               FStar_All.pipe_left
                 (fun _10537  -> FStar_Pervasives_Native.Some _10537)
                 uu____10533
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_ite_lid ->
               let uu____10564 =
                 let uu____10565 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_ite uu____10565 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10568  -> FStar_Pervasives_Native.Some _10568)
                 uu____10564
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_close_lid ->
               let uu____10595 =
                 let uu____10596 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_close uu____10596 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10599  -> FStar_Pervasives_Native.Some _10599)
                 uu____10595
           | FStar_Syntax_Syntax.Tm_app (head1,args1) when
               is_fv head1 FStar_Parser_Const.pure_null_lid ->
               let uu____10626 =
                 let uu____10627 = us_of head1  in
                 mk_app1 FStar_Parser_Const.as_ens_null uu____10627 args1 r
                  in
               FStar_All.pipe_left
                 (fun _10630  -> FStar_Pervasives_Native.Some _10630)
                 uu____10626
           | uu____10631 -> FStar_Pervasives_Native.None)
         in
      let uu____10632 =
        let uu____10633 = FStar_Syntax_Subst.compress t  in
        uu____10633.FStar_Syntax_Syntax.n  in
      match uu____10632 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) when
          is_fv head1 FStar_Parser_Const.as_requires_opaque ->
          reduce_as_requires args t.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_app (head1,args) when
          is_fv head1 FStar_Parser_Const.as_ensures_opaque ->
          reduce_as_ensures args t.FStar_Syntax_Syntax.pos
      | uu____10690 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____10969 ->
                   let uu____10992 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____10992
               | uu____10995 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____11005  ->
               let uu____11006 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____11008 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____11010 = FStar_Syntax_Print.term_to_string t1  in
               let uu____11012 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____11020 =
                 let uu____11022 =
                   let uu____11025 = firstn (Prims.of_int (4)) stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst
                     uu____11025
                    in
                 stack_to_string uu____11022  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____11006 uu____11008 uu____11010 uu____11012 uu____11020);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____11053  ->
               let uu____11054 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____11054);
          (let t_opt = is_wp_req_ens_commutation cfg t1  in
           let uu____11060 = FStar_All.pipe_right t_opt FStar_Util.is_some
              in
           if uu____11060
           then
             ((let uu____11067 =
                 FStar_All.pipe_left
                   (FStar_TypeChecker_Env.debug
                      cfg.FStar_TypeChecker_Cfg.tcenv)
                   (FStar_Options.Other "WPReqEns")
                  in
               if uu____11067
               then
                 let uu____11072 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____11074 =
                   let uu____11076 =
                     FStar_All.pipe_right t_opt FStar_Util.must  in
                   FStar_All.pipe_right uu____11076
                     FStar_Syntax_Print.term_to_string
                    in
                 FStar_Util.print2
                   "Norm request identified as wp_req_ens commutation{, \n\nreduced %s \n\nto\n\n %s\n"
                   uu____11072 uu____11074
               else ());
              (let t2 = FStar_All.pipe_right t_opt FStar_Util.must  in
               let cfg_restricted =
                 FStar_TypeChecker_Cfg.config' []
                   [FStar_TypeChecker_Env.UnfoldAttr
                      [FStar_Parser_Const.wp_req_ens_attr]]
                   cfg.FStar_TypeChecker_Cfg.tcenv
                  in
               let t3 = norm cfg_restricted env [] t2  in
               (let uu____11089 =
                  FStar_All.pipe_left
                    (FStar_TypeChecker_Env.debug
                       cfg.FStar_TypeChecker_Cfg.tcenv)
                    (FStar_Options.Other "WPReqEns")
                   in
                if uu____11089
                then
                  let uu____11094 = FStar_Syntax_Print.term_to_string t3  in
                  FStar_Util.print1
                    "After norm in a restricted environment, t : %s\n}"
                    uu____11094
                else ());
               norm cfg env stack t3))
           else
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11104  ->
                        let uu____11105 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11105);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_constant uu____11108 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11112  ->
                        let uu____11113 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11113);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_name uu____11116 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11120  ->
                        let uu____11121 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11121);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_lazy uu____11124 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11128  ->
                        let uu____11129 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11129);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = uu____11132;
                    FStar_Syntax_Syntax.fv_delta = uu____11133;
                    FStar_Syntax_Syntax.fv_qual =
                      FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Data_ctor );_}
                  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11137  ->
                        let uu____11138 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11138);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = uu____11141;
                    FStar_Syntax_Syntax.fv_delta = uu____11142;
                    FStar_Syntax_Syntax.fv_qual =
                      FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor uu____11143);_}
                  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____11153  ->
                        let uu____11154 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____11154);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                  let qninfo =
                    FStar_TypeChecker_Env.lookup_qname
                      cfg.FStar_TypeChecker_Cfg.tcenv lid
                     in
                  let uu____11160 =
                    FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
                  (match uu____11160 with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Delta_constant_at_level _11163)
                       when _11163 = Prims.int_zero ->
                       (FStar_TypeChecker_Cfg.log_unfolding cfg
                          (fun uu____11167  ->
                             let uu____11168 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                               uu____11168);
                        rebuild cfg env stack t1)
                   | uu____11171 ->
                       let uu____11174 =
                         decide_unfolding cfg env stack
                           t1.FStar_Syntax_Syntax.pos fv qninfo
                          in
                       (match uu____11174 with
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
                  let uu____11213 = closure_as_term cfg env t2  in
                  rebuild cfg env stack uu____11213
              | FStar_Syntax_Syntax.Tm_app (hd1,args) when
                  (should_consider_norm_requests cfg) &&
                    (let uu____11241 = is_norm_request hd1 args  in
                     uu____11241 = Norm_request_requires_rejig)
                  ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     FStar_Util.print_string "Rejigging norm request ... \n"
                   else ();
                   (let uu____11247 = rejig_norm_request hd1 args  in
                    norm cfg env stack uu____11247))
              | FStar_Syntax_Syntax.Tm_app (hd1,args) when
                  (should_consider_norm_requests cfg) &&
                    (let uu____11275 = is_norm_request hd1 args  in
                     uu____11275 = Norm_request_ready)
                  ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     FStar_Util.print_string "Potential norm request ... \n"
                   else ();
                   (let cfg' =
                      let uu___1438_11282 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (let uu___1440_11285 =
                             cfg.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               false;
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1440_11285.FStar_TypeChecker_Cfg.for_extraction)
                           });
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1438_11282.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1438_11282.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          [FStar_TypeChecker_Env.Unfold
                             FStar_Syntax_Syntax.delta_constant];
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1438_11282.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1438_11282.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1438_11282.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___1438_11282.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let uu____11292 =
                      get_norm_request cfg (norm cfg' env []) args  in
                    match uu____11292 with
                    | FStar_Pervasives_Native.None  ->
                        (if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           FStar_Util.print_string "Norm request None ... \n"
                         else ();
                         (let stack1 =
                            FStar_All.pipe_right stack
                              (FStar_List.fold_right
                                 (fun uu____11328  ->
                                    fun stack1  ->
                                      match uu____11328 with
                                      | (a,aq) ->
                                          let uu____11340 =
                                            let uu____11341 =
                                              let uu____11348 =
                                                let uu____11349 =
                                                  let uu____11381 =
                                                    FStar_Util.mk_ref
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  (env, a, uu____11381,
                                                    false)
                                                   in
                                                Clos uu____11349  in
                                              (uu____11348, aq,
                                                (t1.FStar_Syntax_Syntax.pos))
                                               in
                                            Arg uu____11341  in
                                          uu____11340 :: stack1) args)
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____11449  ->
                               let uu____11450 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length args)
                                  in
                               FStar_Util.print1 "\tPushed %s arguments\n"
                                 uu____11450);
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
                            let uu____11482 =
                              let uu____11484 =
                                let uu____11486 =
                                  FStar_Util.time_diff start fin  in
                                FStar_Pervasives_Native.snd uu____11486  in
                              FStar_Util.string_of_int uu____11484  in
                            let uu____11493 =
                              FStar_Syntax_Print.term_to_string tm'  in
                            let uu____11495 =
                              FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                            let uu____11497 =
                              FStar_Syntax_Print.term_to_string tm_norm  in
                            FStar_Util.print4
                              "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                              uu____11482 uu____11493 uu____11495 uu____11497)
                         else ();
                         rebuild cfg env stack tm_norm)
                    | FStar_Pervasives_Native.Some (s,tm) ->
                        let delta_level =
                          let uu____11517 =
                            FStar_All.pipe_right s
                              (FStar_Util.for_some
                                 (fun uu___13_11524  ->
                                    match uu___13_11524 with
                                    | FStar_TypeChecker_Env.UnfoldUntil
                                        uu____11526 -> true
                                    | FStar_TypeChecker_Env.UnfoldOnly
                                        uu____11528 -> true
                                    | FStar_TypeChecker_Env.UnfoldFully
                                        uu____11532 -> true
                                    | uu____11536 -> false))
                             in
                          if uu____11517
                          then
                            [FStar_TypeChecker_Env.Unfold
                               FStar_Syntax_Syntax.delta_constant]
                          else [FStar_TypeChecker_Env.NoDelta]  in
                        let cfg'1 =
                          let uu___1478_11544 = cfg  in
                          let uu____11545 =
                            let uu___1480_11546 =
                              FStar_TypeChecker_Cfg.to_fsteps s  in
                            {
                              FStar_TypeChecker_Cfg.beta =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.beta);
                              FStar_TypeChecker_Cfg.iota =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.iota);
                              FStar_TypeChecker_Cfg.zeta =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.zeta);
                              FStar_TypeChecker_Cfg.weak =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.weak);
                              FStar_TypeChecker_Cfg.hnf =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.hnf);
                              FStar_TypeChecker_Cfg.primops =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.primops);
                              FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                              FStar_TypeChecker_Cfg.unfold_until =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.unfold_until);
                              FStar_TypeChecker_Cfg.unfold_only =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.unfold_only);
                              FStar_TypeChecker_Cfg.unfold_fully =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.unfold_fully);
                              FStar_TypeChecker_Cfg.unfold_attr =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.unfold_attr);
                              FStar_TypeChecker_Cfg.unfold_tac =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.unfold_tac);
                              FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                              FStar_TypeChecker_Cfg.simplify =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.simplify);
                              FStar_TypeChecker_Cfg.erase_universes =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.erase_universes);
                              FStar_TypeChecker_Cfg.allow_unbound_universes =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.allow_unbound_universes);
                              FStar_TypeChecker_Cfg.reify_ =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.reify_);
                              FStar_TypeChecker_Cfg.compress_uvars =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.compress_uvars);
                              FStar_TypeChecker_Cfg.no_full_norm =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.no_full_norm);
                              FStar_TypeChecker_Cfg.check_no_uvars =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.check_no_uvars);
                              FStar_TypeChecker_Cfg.unmeta =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.unmeta);
                              FStar_TypeChecker_Cfg.unascribe =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.unascribe);
                              FStar_TypeChecker_Cfg.in_full_norm_request =
                                true;
                              FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                              FStar_TypeChecker_Cfg.nbe_step =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.nbe_step);
                              FStar_TypeChecker_Cfg.for_extraction =
                                (uu___1480_11546.FStar_TypeChecker_Cfg.for_extraction)
                            }  in
                          {
                            FStar_TypeChecker_Cfg.steps = uu____11545;
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___1478_11544.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___1478_11544.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level = delta_level;
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___1478_11544.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___1478_11544.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___1478_11544.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                            FStar_TypeChecker_Cfg.reifying =
                              (uu___1478_11544.FStar_TypeChecker_Cfg.reifying)
                          }  in
                        let stack' =
                          let tail1 = (Cfg cfg) :: stack  in
                          if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                          then
                            let uu____11554 =
                              let uu____11555 =
                                let uu____11560 = FStar_Util.now ()  in
                                (tm, uu____11560)  in
                              Debug uu____11555  in
                            uu____11554 :: tail1
                          else tail1  in
                        norm cfg'1 env stack' tm))
              | FStar_Syntax_Syntax.Tm_type u ->
                  let u1 = norm_universe cfg env u  in
                  let uu____11565 =
                    mk (FStar_Syntax_Syntax.Tm_type u1)
                      t1.FStar_Syntax_Syntax.pos
                     in
                  rebuild cfg env stack uu____11565
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                  then norm cfg env stack t'
                  else
                    (let us1 =
                       let uu____11576 =
                         let uu____11583 =
                           FStar_List.map (norm_universe cfg env) us  in
                         (uu____11583, (t1.FStar_Syntax_Syntax.pos))  in
                       UnivArgs uu____11576  in
                     let stack1 = us1 :: stack  in norm cfg env stack1 t')
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____11592 = lookup_bvar env x  in
                  (match uu____11592 with
                   | Univ uu____11593 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> failwith "Term variable not found"
                   | Clos (env1,t0,r,fix) ->
                       if
                         (Prims.op_Negation fix) ||
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                       then
                         let uu____11647 = FStar_ST.op_Bang r  in
                         (match uu____11647 with
                          | FStar_Pervasives_Native.Some (env2,t') ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11743  ->
                                    let uu____11744 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____11746 =
                                      FStar_Syntax_Print.term_to_string t'
                                       in
                                    FStar_Util.print2
                                      "Lazy hit: %s cached to %s\n"
                                      uu____11744 uu____11746);
                               (let uu____11749 = maybe_weakly_reduced t'  in
                                if uu____11749
                                then
                                  match stack with
                                  | [] when
                                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                        ||
                                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                      -> rebuild cfg env2 stack t'
                                  | uu____11752 -> norm cfg env2 stack t'
                                else rebuild cfg env2 stack t'))
                          | FStar_Pervasives_Native.None  ->
                              norm cfg env1 ((MemoLazy r) :: stack) t0)
                       else norm cfg env1 stack t0)
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  (match stack with
                   | (UnivArgs uu____11796)::uu____11797 ->
                       failwith
                         "Ill-typed term: universes cannot be applied to term abstraction"
                   | (Arg (c,uu____11808,uu____11809))::stack_rest ->
                       (match c with
                        | Univ uu____11813 ->
                            norm cfg ((FStar_Pervasives_Native.None, c) ::
                              env) stack_rest t1
                        | uu____11822 ->
                            (match bs with
                             | [] -> failwith "Impossible"
                             | b::[] ->
                                 (FStar_TypeChecker_Cfg.log cfg
                                    (fun uu____11852  ->
                                       let uu____11853 = closure_to_string c
                                          in
                                       FStar_Util.print1 "\tShifted %s\n"
                                         uu____11853);
                                  norm cfg
                                    (((FStar_Pervasives_Native.Some b), c) ::
                                    env) stack_rest body)
                             | b::tl1 ->
                                 (FStar_TypeChecker_Cfg.log cfg
                                    (fun uu____11889  ->
                                       let uu____11890 = closure_to_string c
                                          in
                                       FStar_Util.print1 "\tShifted %s\n"
                                         uu____11890);
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
                          (fun uu____11938  ->
                             let uu____11939 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.print1 "\tSet memo %s\n" uu____11939);
                        norm cfg env stack1 t1)
                   | (Match uu____11942)::uu____11943 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____11958 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____11958 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____11994  -> dummy :: env1)
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
                                             let uu____12038 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12038)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1598_12046 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1598_12046.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1598_12046.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12047 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12053  ->
                                    let uu____12054 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12054);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1605_12069 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1605_12069.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1605_12069.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1605_12069.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1605_12069.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1605_12069.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1605_12069.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1605_12069.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1605_12069.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Debug uu____12073)::uu____12074 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12085 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12085 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12121  -> dummy :: env1)
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
                                             let uu____12165 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12165)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1598_12173 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1598_12173.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1598_12173.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12174 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12180  ->
                                    let uu____12181 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12181);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1605_12196 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1605_12196.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1605_12196.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1605_12196.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1605_12196.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1605_12196.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1605_12196.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1605_12196.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1605_12196.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Meta uu____12200)::uu____12201 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12214 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12214 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12250  -> dummy :: env1)
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
                                             let uu____12294 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12294)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1598_12302 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1598_12302.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1598_12302.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12303 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12309  ->
                                    let uu____12310 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12310);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1605_12325 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1605_12325.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1605_12325.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1605_12325.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1605_12325.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1605_12325.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1605_12325.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1605_12325.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1605_12325.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Let uu____12329)::uu____12330 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12345 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12345 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12381  -> dummy :: env1)
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
                                             let uu____12425 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12425)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1598_12433 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1598_12433.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1598_12433.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12434 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12440  ->
                                    let uu____12441 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12441);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1605_12456 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1605_12456.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1605_12456.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1605_12456.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1605_12456.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1605_12456.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1605_12456.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1605_12456.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1605_12456.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (App uu____12460)::uu____12461 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12476 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12476 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12512  -> dummy :: env1)
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
                                             let uu____12556 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12556)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1598_12564 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1598_12564.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1598_12564.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12565 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12571  ->
                                    let uu____12572 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12572);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1605_12587 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1605_12587.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1605_12587.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1605_12587.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1605_12587.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1605_12587.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1605_12587.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1605_12587.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1605_12587.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Abs uu____12591)::uu____12592 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____12611 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12611 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12647  -> dummy :: env1)
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
                                             let uu____12691 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12691)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1598_12699 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1598_12699.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1598_12699.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12700 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12706  ->
                                    let uu____12707 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12707);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1605_12722 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1605_12722.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1605_12722.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1605_12722.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1605_12722.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1605_12722.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1605_12722.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1605_12722.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1605_12722.FStar_TypeChecker_Cfg.reifying)
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
                         (let uu____12730 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____12730 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____12766  -> dummy :: env1)
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
                                             let uu____12810 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____12810)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1598_12818 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1598_12818.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1598_12818.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____12819 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____12825  ->
                                    let uu____12826 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____12826);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1605_12841 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1605_12841.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1605_12841.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1605_12841.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1605_12841.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1605_12841.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1605_12841.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1605_12841.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1605_12841.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1))))
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let strict_args =
                    let uu____12877 =
                      let uu____12878 = FStar_Syntax_Util.un_uinst head1  in
                      uu____12878.FStar_Syntax_Syntax.n  in
                    match uu____12877 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_TypeChecker_Env.fv_has_strict_args
                          cfg.FStar_TypeChecker_Cfg.tcenv fv
                    | uu____12887 -> FStar_Pervasives_Native.None  in
                  (match strict_args with
                   | FStar_Pervasives_Native.None  ->
                       let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____12908  ->
                                 fun stack1  ->
                                   match uu____12908 with
                                   | (a,aq) ->
                                       let uu____12920 =
                                         let uu____12921 =
                                           let uu____12928 =
                                             let uu____12929 =
                                               let uu____12961 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____12961, false)
                                                in
                                             Clos uu____12929  in
                                           (uu____12928, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____12921  in
                                       uu____12920 :: stack1) args)
                          in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13029  ->
                             let uu____13030 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length args)
                                in
                             FStar_Util.print1 "\tPushed %s arguments\n"
                               uu____13030);
                        norm cfg env stack1 head1)
                   | FStar_Pervasives_Native.Some strict_args1 ->
                       let norm_args =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____13081  ->
                                 match uu____13081 with
                                 | (a,i) ->
                                     let uu____13092 = norm cfg env [] a  in
                                     (uu____13092, i)))
                          in
                       let norm_args_len = FStar_List.length norm_args  in
                       let uu____13098 =
                         FStar_All.pipe_right strict_args1
                           (FStar_List.for_all
                              (fun i  ->
                                 if i >= norm_args_len
                                 then false
                                 else
                                   (let uu____13113 =
                                      FStar_List.nth norm_args i  in
                                    match uu____13113 with
                                    | (arg_i,uu____13124) ->
                                        let uu____13125 =
                                          FStar_Syntax_Util.head_and_args
                                            arg_i
                                           in
                                        (match uu____13125 with
                                         | (head2,uu____13144) ->
                                             let uu____13169 =
                                               let uu____13170 =
                                                 FStar_Syntax_Util.un_uinst
                                                   head2
                                                  in
                                               uu____13170.FStar_Syntax_Syntax.n
                                                in
                                             (match uu____13169 with
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____13174 -> true
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv ->
                                                  let uu____13177 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Env.is_datacon
                                                    cfg.FStar_TypeChecker_Cfg.tcenv
                                                    uu____13177
                                              | uu____13178 -> false)))))
                          in
                       if uu____13098
                       then
                         let stack1 =
                           FStar_All.pipe_right stack
                             (FStar_List.fold_right
                                (fun uu____13195  ->
                                   fun stack1  ->
                                     match uu____13195 with
                                     | (a,aq) ->
                                         let uu____13207 =
                                           let uu____13208 =
                                             let uu____13215 =
                                               let uu____13216 =
                                                 let uu____13248 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], a))
                                                    in
                                                 (env, a, uu____13248, false)
                                                  in
                                               Clos uu____13216  in
                                             (uu____13215, aq,
                                               (t1.FStar_Syntax_Syntax.pos))
                                              in
                                           Arg uu____13208  in
                                         uu____13207 :: stack1) norm_args)
                            in
                         (FStar_TypeChecker_Cfg.log cfg
                            (fun uu____13330  ->
                               let uu____13331 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length args)
                                  in
                               FStar_Util.print1 "\tPushed %s arguments\n"
                                 uu____13331);
                          norm cfg env stack1 head1)
                       else
                         (let head2 = closure_as_term cfg env head1  in
                          let term =
                            FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                              FStar_Pervasives_Native.None
                              t1.FStar_Syntax_Syntax.pos
                             in
                          rebuild cfg env stack term))
              | FStar_Syntax_Syntax.Tm_refine (x,uu____13351) when
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
                                ((let uu___1667_13396 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1667_13396.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1667_13396.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t_x
                                  }), f)) t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild cfg env stack t2
                     | uu____13397 ->
                         let uu____13412 = closure_as_term cfg env t1  in
                         rebuild cfg env stack uu____13412)
                  else
                    (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                     let uu____13416 =
                       FStar_Syntax_Subst.open_term
                         [(x, FStar_Pervasives_Native.None)] f
                        in
                     match uu____13416 with
                     | (closing,f1) ->
                         let f2 = norm cfg (dummy :: env) [] f1  in
                         let t2 =
                           let uu____13447 =
                             let uu____13448 =
                               let uu____13455 =
                                 FStar_Syntax_Subst.close closing f2  in
                               ((let uu___1676_13461 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1676_13461.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1676_13461.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t_x
                                 }), uu____13455)
                                in
                             FStar_Syntax_Syntax.Tm_refine uu____13448  in
                           mk uu____13447 t1.FStar_Syntax_Syntax.pos  in
                         rebuild cfg env stack t2)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                  then
                    let uu____13485 = closure_as_term cfg env t1  in
                    rebuild cfg env stack uu____13485
                  else
                    (let uu____13488 = FStar_Syntax_Subst.open_comp bs c  in
                     match uu____13488 with
                     | (bs1,c1) ->
                         let c2 =
                           let uu____13496 =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13522  -> dummy :: env1) env)
                              in
                           norm_comp cfg uu____13496 c1  in
                         let t2 =
                           let uu____13546 = norm_binders cfg env bs1  in
                           FStar_Syntax_Util.arrow uu____13546 c2  in
                         rebuild cfg env stack t2)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
                  -> norm cfg env stack t11
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
                  (match stack with
                   | (Match uu____13659)::uu____13660 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13673  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (Arg uu____13675)::uu____13676 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13687  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (App
                       (uu____13689,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_reify );
                                      FStar_Syntax_Syntax.pos = uu____13690;
                                      FStar_Syntax_Syntax.vars = uu____13691;_},uu____13692,uu____13693))::uu____13694
                       when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13701  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (MemoLazy uu____13703)::uu____13704 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13715  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | uu____13717 ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____13720  ->
                             FStar_Util.print_string
                               "+++ Keeping ascription \n");
                        (let t12 = norm cfg env [] t11  in
                         FStar_TypeChecker_Cfg.log cfg
                           (fun uu____13725  ->
                              FStar_Util.print_string
                                "+++ Normalizing ascription \n");
                         (let tc1 =
                            match tc with
                            | FStar_Util.Inl t2 ->
                                let uu____13751 = norm cfg env [] t2  in
                                FStar_Util.Inl uu____13751
                            | FStar_Util.Inr c ->
                                let uu____13765 = norm_comp cfg env c  in
                                FStar_Util.Inr uu____13765
                             in
                          let tacopt1 =
                            FStar_Util.map_opt tacopt (norm cfg env [])  in
                          match stack with
                          | (Cfg cfg1)::stack1 ->
                              let t2 =
                                let uu____13788 =
                                  let uu____13789 =
                                    let uu____13816 =
                                      FStar_Syntax_Util.unascribe t12  in
                                    (uu____13816, (tc1, tacopt1), l)  in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____13789
                                   in
                                mk uu____13788 t1.FStar_Syntax_Syntax.pos  in
                              norm cfg1 env stack1 t2
                          | uu____13851 ->
                              let uu____13852 =
                                let uu____13853 =
                                  let uu____13854 =
                                    let uu____13881 =
                                      FStar_Syntax_Util.unascribe t12  in
                                    (uu____13881, (tc1, tacopt1), l)  in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____13854
                                   in
                                mk uu____13853 t1.FStar_Syntax_Syntax.pos  in
                              rebuild cfg env stack uu____13852))))
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
                      let uu___1755_13959 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (let uu___1757_13962 =
                             cfg.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak = true;
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1757_13962.FStar_TypeChecker_Cfg.for_extraction)
                           });
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1755_13959.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1755_13959.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___1755_13959.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1755_13959.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1755_13959.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1755_13959.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___1755_13959.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___1755_13959.FStar_TypeChecker_Cfg.reifying)
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
                            let uu____14003 =
                              FStar_Syntax_Subst.univ_var_opening
                                lb.FStar_Syntax_Syntax.lbunivs
                               in
                            match uu____14003 with
                            | (openings,lbunivs) ->
                                let cfg1 =
                                  let uu___1770_14023 = cfg  in
                                  let uu____14024 =
                                    FStar_TypeChecker_Env.push_univ_vars
                                      cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                     in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1770_14023.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv = uu____14024;
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1770_14023.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1770_14023.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1770_14023.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong =
                                      (uu___1770_14023.FStar_TypeChecker_Cfg.strong);
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1770_14023.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1770_14023.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1770_14023.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                let norm1 t2 =
                                  let uu____14031 =
                                    let uu____14032 =
                                      FStar_Syntax_Subst.subst openings t2
                                       in
                                    norm cfg1 env [] uu____14032  in
                                  FStar_Syntax_Subst.close_univ_vars lbunivs
                                    uu____14031
                                   in
                                let lbtyp =
                                  norm1 lb.FStar_Syntax_Syntax.lbtyp  in
                                let lbdef =
                                  norm1 lb.FStar_Syntax_Syntax.lbdef  in
                                let uu___1777_14035 = lb  in
                                {
                                  FStar_Syntax_Syntax.lbname =
                                    (uu___1777_14035.FStar_Syntax_Syntax.lbname);
                                  FStar_Syntax_Syntax.lbunivs = lbunivs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1777_14035.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = lbdef;
                                  FStar_Syntax_Syntax.lbattrs =
                                    (uu___1777_14035.FStar_Syntax_Syntax.lbattrs);
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1777_14035.FStar_Syntax_Syntax.lbpos)
                                }))
                     in
                  let uu____14036 =
                    mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                      t1.FStar_Syntax_Syntax.pos
                     in
                  rebuild cfg env stack uu____14036
              | FStar_Syntax_Syntax.Tm_let
                  ((uu____14049,{
                                  FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                    uu____14050;
                                  FStar_Syntax_Syntax.lbunivs = uu____14051;
                                  FStar_Syntax_Syntax.lbtyp = uu____14052;
                                  FStar_Syntax_Syntax.lbeff = uu____14053;
                                  FStar_Syntax_Syntax.lbdef = uu____14054;
                                  FStar_Syntax_Syntax.lbattrs = uu____14055;
                                  FStar_Syntax_Syntax.lbpos = uu____14056;_}::uu____14057),uu____14058)
                  -> rebuild cfg env stack t1
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let uu____14103 =
                    FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
                  if uu____14103
                  then
                    let binder =
                      let uu____14107 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.mk_binder uu____14107  in
                    let env1 =
                      let uu____14117 =
                        let uu____14124 =
                          let uu____14125 =
                            let uu____14157 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env, (lb.FStar_Syntax_Syntax.lbdef),
                              uu____14157, false)
                             in
                          Clos uu____14125  in
                        ((FStar_Pervasives_Native.Some binder), uu____14124)
                         in
                      uu____14117 :: env  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____14232  ->
                          FStar_Util.print_string "+++ Reducing Tm_let\n");
                     norm cfg env1 stack body)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____14239  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____14241 = closure_as_term cfg env t1  in
                        rebuild cfg env stack uu____14241))
                    else
                      (let uu____14244 =
                         let uu____14249 =
                           let uu____14250 =
                             let uu____14257 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____14257
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____14250]  in
                         FStar_Syntax_Subst.open_term uu____14249 body  in
                       match uu____14244 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____14284  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____14293 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____14293  in
                               FStar_Util.Inl
                                 (let uu___1818_14309 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1818_14309.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1818_14309.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____14312  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1823_14315 = lb  in
                                let uu____14316 =
                                  norm cfg env []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____14319 =
                                  FStar_List.map (norm cfg env [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1823_14315.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1823_14315.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____14316;
                                  FStar_Syntax_Syntax.lbattrs = uu____14319;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1823_14315.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____14354  -> dummy :: env1)
                                     env)
                                 in
                              let stack1 = (Cfg cfg) :: stack  in
                              let cfg1 =
                                let uu___1830_14379 = cfg  in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1830_14379.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1830_14379.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1830_14379.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1830_14379.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1830_14379.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1830_14379.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1830_14379.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1830_14379.FStar_TypeChecker_Cfg.reifying)
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____14383  ->
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
                  let uu____14404 = FStar_Syntax_Subst.open_let_rec lbs body
                     in
                  (match uu____14404 with
                   | (lbs1,body1) ->
                       let lbs2 =
                         FStar_List.map
                           (fun lb  ->
                              let ty =
                                norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                 in
                              let lbname =
                                let uu____14440 =
                                  let uu___1846_14441 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1846_14441.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1846_14441.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  }  in
                                FStar_Util.Inl uu____14440  in
                              let uu____14442 =
                                FStar_Syntax_Util.abs_formals
                                  lb.FStar_Syntax_Syntax.lbdef
                                 in
                              match uu____14442 with
                              | (xs,def_body,lopt) ->
                                  let xs1 = norm_binders cfg env xs  in
                                  let env1 =
                                    let uu____14468 =
                                      FStar_List.map
                                        (fun uu____14490  -> dummy) xs1
                                       in
                                    let uu____14497 =
                                      let uu____14506 =
                                        FStar_List.map
                                          (fun uu____14522  -> dummy) lbs1
                                         in
                                      FStar_List.append uu____14506 env  in
                                    FStar_List.append uu____14468 uu____14497
                                     in
                                  let def_body1 = norm cfg env1 [] def_body
                                     in
                                  let lopt1 =
                                    match lopt with
                                    | FStar_Pervasives_Native.Some rc ->
                                        let uu____14542 =
                                          let uu___1860_14543 = rc  in
                                          let uu____14544 =
                                            FStar_Util.map_opt
                                              rc.FStar_Syntax_Syntax.residual_typ
                                              (norm cfg env1 [])
                                             in
                                          {
                                            FStar_Syntax_Syntax.residual_effect
                                              =
                                              (uu___1860_14543.FStar_Syntax_Syntax.residual_effect);
                                            FStar_Syntax_Syntax.residual_typ
                                              = uu____14544;
                                            FStar_Syntax_Syntax.residual_flags
                                              =
                                              (uu___1860_14543.FStar_Syntax_Syntax.residual_flags)
                                          }  in
                                        FStar_Pervasives_Native.Some
                                          uu____14542
                                    | uu____14553 -> lopt  in
                                  let def =
                                    FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                     in
                                  let uu___1865_14559 = lb  in
                                  {
                                    FStar_Syntax_Syntax.lbname = lbname;
                                    FStar_Syntax_Syntax.lbunivs =
                                      (uu___1865_14559.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp = ty;
                                    FStar_Syntax_Syntax.lbeff =
                                      (uu___1865_14559.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs =
                                      (uu___1865_14559.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (uu___1865_14559.FStar_Syntax_Syntax.lbpos)
                                  }) lbs1
                          in
                       let env' =
                         let uu____14569 =
                           FStar_List.map (fun uu____14585  -> dummy) lbs2
                            in
                         FStar_List.append uu____14569 env  in
                       let body2 = norm cfg env' [] body1  in
                       let uu____14593 =
                         FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                       (match uu____14593 with
                        | (lbs3,body3) ->
                            let t2 =
                              let uu___1874_14609 = t1  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_let
                                     ((true, lbs3), body3));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1874_14609.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1874_14609.FStar_Syntax_Syntax.vars)
                              }  in
                            rebuild cfg env stack t2))
              | FStar_Syntax_Syntax.Tm_let (lbs,body) when
                  Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                  ->
                  let uu____14643 = closure_as_term cfg env t1  in
                  rebuild cfg env stack uu____14643
              | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
                  let uu____14664 =
                    FStar_List.fold_right
                      (fun lb  ->
                         fun uu____14742  ->
                           match uu____14742 with
                           | (rec_env,memos,i) ->
                               let bv =
                                 let uu___1890_14867 =
                                   FStar_Util.left
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1890_14867.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index = i;
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1890_14867.FStar_Syntax_Syntax.sort)
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
                  (match uu____14664 with
                   | (rec_env,memos,uu____15058) ->
                       let uu____15113 =
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
                                let uu____15362 =
                                  let uu____15369 =
                                    let uu____15370 =
                                      let uu____15402 =
                                        FStar_Util.mk_ref
                                          FStar_Pervasives_Native.None
                                         in
                                      (rec_env,
                                        (lb.FStar_Syntax_Syntax.lbdef),
                                        uu____15402, false)
                                       in
                                    Clos uu____15370  in
                                  (FStar_Pervasives_Native.None, uu____15369)
                                   in
                                uu____15362 :: env1)
                           (FStar_Pervasives_Native.snd lbs) env
                          in
                       norm cfg body_env stack body)
              | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____15487  ->
                        let uu____15488 =
                          FStar_Syntax_Print.metadata_to_string m  in
                        FStar_Util.print1 ">> metadata = %s\n" uu____15488);
                   (match m with
                    | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                        reduce_impure_comp cfg env stack head1
                          (FStar_Util.Inl m1) t2
                    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                        reduce_impure_comp cfg env stack head1
                          (FStar_Util.Inr (m1, m')) t2
                    | uu____15512 ->
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                        then norm cfg env stack head1
                        else
                          (match stack with
                           | uu____15516::uu____15517 ->
                               (match m with
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (l,r,uu____15522) ->
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
                                | uu____15601 -> norm cfg env stack head1)
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
                                     let uu____15649 =
                                       let uu____15670 =
                                         norm_pattern_args cfg env args  in
                                       (names2, uu____15670)  in
                                     FStar_Syntax_Syntax.Meta_pattern
                                       uu____15649
                                 | uu____15699 -> m  in
                               let t2 =
                                 mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                   t1.FStar_Syntax_Syntax.pos
                                  in
                               rebuild cfg env stack t2)))
              | FStar_Syntax_Syntax.Tm_delayed uu____15705 ->
                  let t2 = FStar_Syntax_Subst.compress t1  in
                  norm cfg env stack t2
              | FStar_Syntax_Syntax.Tm_uvar uu____15729 ->
                  let t2 = FStar_Syntax_Subst.compress t1  in
                  (match t2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar uu____15743 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                       then
                         let uu____15757 =
                           let uu____15759 =
                             FStar_Range.string_of_range
                               t2.FStar_Syntax_Syntax.pos
                              in
                           let uu____15761 =
                             FStar_Syntax_Print.term_to_string t2  in
                           FStar_Util.format2
                             "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                             uu____15759 uu____15761
                            in
                         failwith uu____15757
                       else
                         (let uu____15766 = inline_closure_env cfg env [] t2
                             in
                          rebuild cfg env stack uu____15766)
                   | uu____15767 -> norm cfg env stack t2)))

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
              let uu____15776 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____15776 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____15790  ->
                        let uu____15791 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____15791);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____15804  ->
                        let uu____15805 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____15807 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____15805 uu____15807);
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
                      | (UnivArgs (us',uu____15820))::stack1 ->
                          ((let uu____15829 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____15829
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____15837 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____15837) us'
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
                      | uu____15873 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____15876 ->
                          let uu____15879 =
                            let uu____15881 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____15881
                             in
                          failwith uu____15879
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
                  let uu___2002_15909 = cfg  in
                  let uu____15910 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____15910;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___2002_15909.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___2002_15909.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___2002_15909.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___2002_15909.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___2002_15909.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___2002_15909.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___2002_15909.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____15941,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____15942;
                                    FStar_Syntax_Syntax.vars = uu____15943;_},uu____15944,uu____15945))::uu____15946
                     -> ()
                 | uu____15951 ->
                     let uu____15954 =
                       let uu____15956 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____15956
                        in
                     failwith uu____15954);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____15965  ->
                      let uu____15966 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____15968 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____15966
                        uu____15968);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____15972 =
                    let uu____15973 = FStar_Syntax_Subst.compress head3  in
                    uu____15973.FStar_Syntax_Syntax.n  in
                  match uu____15972 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____15994 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____15994
                         in
                      let uu____15995 =
                        let uu____16004 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_bind_repr
                           in
                        FStar_All.pipe_right uu____16004 FStar_Util.must  in
                      (match uu____15995 with
                       | (uu____16019,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____16029 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____16040 =
                                    let uu____16041 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____16041.FStar_Syntax_Syntax.n  in
                                  match uu____16040 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____16047,uu____16048))
                                      ->
                                      let uu____16057 =
                                        let uu____16058 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____16058.FStar_Syntax_Syntax.n  in
                                      (match uu____16057 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____16064,msrc,uu____16066))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____16075 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____16075
                                       | uu____16076 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____16077 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____16078 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____16078 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___2074_16083 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___2074_16083.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___2074_16083.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___2074_16083.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___2074_16083.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___2074_16083.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____16084 = FStar_List.tl stack
                                        in
                                     let uu____16085 =
                                       let uu____16086 =
                                         let uu____16093 =
                                           let uu____16094 =
                                             let uu____16108 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____16108)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____16094
                                            in
                                         FStar_Syntax_Syntax.mk uu____16093
                                          in
                                       uu____16086
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____16084 uu____16085
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____16124 =
                                       let uu____16126 = is_return body  in
                                       match uu____16126 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____16131;
                                             FStar_Syntax_Syntax.vars =
                                               uu____16132;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____16135 -> false  in
                                     if uu____16124
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
                                          let uu____16159 =
                                            let uu____16166 =
                                              let uu____16167 =
                                                let uu____16186 =
                                                  let uu____16195 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____16195]  in
                                                (uu____16186, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____16167
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____16166
                                             in
                                          uu____16159
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____16234 =
                                            let uu____16235 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____16235.FStar_Syntax_Syntax.n
                                             in
                                          match uu____16234 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____16241::uu____16242::[])
                                              ->
                                              let uu____16247 =
                                                let uu____16254 =
                                                  let uu____16255 =
                                                    let uu____16262 =
                                                      let uu____16263 =
                                                        let uu____16264 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____16264
                                                         in
                                                      let uu____16265 =
                                                        let uu____16268 =
                                                          let uu____16269 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____16269
                                                           in
                                                        [uu____16268]  in
                                                      uu____16263 ::
                                                        uu____16265
                                                       in
                                                    (bind1, uu____16262)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____16255
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____16254
                                                 in
                                              uu____16247
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____16272 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____16287 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____16287
                                          then
                                            let uu____16300 =
                                              let uu____16309 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____16309
                                               in
                                            let uu____16310 =
                                              let uu____16321 =
                                                let uu____16330 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____16330
                                                 in
                                              [uu____16321]  in
                                            uu____16300 :: uu____16310
                                          else []  in
                                        let reified =
                                          let args =
                                            let uu____16379 =
                                              FStar_Syntax_Util.is_layered ed
                                               in
                                            if uu____16379
                                            then
                                              let unit_args =
                                                let uu____16403 =
                                                  let uu____16404 =
                                                    let uu____16407 =
                                                      let uu____16408 =
                                                        FStar_All.pipe_right
                                                          ed
                                                          FStar_Syntax_Util.get_bind_vc_combinator
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____16408
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____16407
                                                      FStar_Syntax_Subst.compress
                                                     in
                                                  uu____16404.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____16403 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (uu____16449::uu____16450::bs,uu____16452)
                                                    when
                                                    (FStar_List.length bs) >=
                                                      (Prims.of_int (2))
                                                    ->
                                                    let uu____16504 =
                                                      let uu____16513 =
                                                        FStar_All.pipe_right
                                                          bs
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs)
                                                                -
                                                                (Prims.of_int (2))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____16513
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____16504
                                                      (FStar_List.map
                                                         (fun uu____16644  ->
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.unit_const))
                                                | uu____16651 ->
                                                    let uu____16652 =
                                                      let uu____16658 =
                                                        let uu____16660 =
                                                          FStar_Ident.string_of_lid
                                                            ed.FStar_Syntax_Syntax.mname
                                                           in
                                                        let uu____16662 =
                                                          let uu____16664 =
                                                            let uu____16665 =
                                                              FStar_All.pipe_right
                                                                ed
                                                                FStar_Syntax_Util.get_bind_vc_combinator
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____16665
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____16664
                                                            FStar_Syntax_Print.term_to_string
                                                           in
                                                        FStar_Util.format2
                                                          "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                          uu____16660
                                                          uu____16662
                                                         in
                                                      (FStar_Errors.Fatal_UnexpectedEffect,
                                                        uu____16658)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____16652 rng
                                                 in
                                              let uu____16699 =
                                                FStar_Syntax_Syntax.as_arg
                                                  lb.FStar_Syntax_Syntax.lbtyp
                                                 in
                                              let uu____16708 =
                                                let uu____16719 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____16728 =
                                                  let uu____16739 =
                                                    let uu____16750 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head4
                                                       in
                                                    let uu____16759 =
                                                      let uu____16770 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          body2
                                                         in
                                                      [uu____16770]  in
                                                    uu____16750 ::
                                                      uu____16759
                                                     in
                                                  FStar_List.append unit_args
                                                    uu____16739
                                                   in
                                                uu____16719 :: uu____16728
                                                 in
                                              uu____16699 :: uu____16708
                                            else
                                              (let uu____16829 =
                                                 let uu____16840 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____16849 =
                                                   let uu____16860 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   [uu____16860]  in
                                                 uu____16840 :: uu____16849
                                                  in
                                               let uu____16893 =
                                                 let uu____16904 =
                                                   let uu____16915 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       FStar_Syntax_Syntax.tun
                                                      in
                                                   let uu____16924 =
                                                     let uu____16935 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         head4
                                                        in
                                                     let uu____16944 =
                                                       let uu____16955 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let uu____16964 =
                                                         let uu____16975 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2
                                                            in
                                                         [uu____16975]  in
                                                       uu____16955 ::
                                                         uu____16964
                                                        in
                                                     uu____16935 ::
                                                       uu____16944
                                                      in
                                                   uu____16915 :: uu____16924
                                                    in
                                                 FStar_List.append
                                                   maybe_range_arg
                                                   uu____16904
                                                  in
                                               FStar_List.append uu____16829
                                                 uu____16893)
                                             in
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (bind_inst, args))
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____17056  ->
                                             let uu____17057 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____17059 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____17057 uu____17059);
                                        (let uu____17062 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____17062 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____17090 = FStar_Options.defensive ()  in
                        if uu____17090
                        then
                          let is_arg_impure uu____17105 =
                            match uu____17105 with
                            | (e,q) ->
                                let uu____17119 =
                                  let uu____17120 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____17120.FStar_Syntax_Syntax.n  in
                                (match uu____17119 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____17136 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____17136
                                 | uu____17138 -> false)
                             in
                          let uu____17140 =
                            let uu____17142 =
                              let uu____17153 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____17153 :: args  in
                            FStar_Util.for_some is_arg_impure uu____17142  in
                          (if uu____17140
                           then
                             let uu____17179 =
                               let uu____17185 =
                                 let uu____17187 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____17187
                                  in
                               (FStar_Errors.Warning_Defensive, uu____17185)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____17179
                           else ())
                        else ());
                       (let fallback1 uu____17200 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____17204  ->
                               let uu____17205 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____17205 "");
                          (let uu____17209 = FStar_List.tl stack  in
                           let uu____17210 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____17209 uu____17210)
                           in
                        let fallback2 uu____17216 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____17220  ->
                               let uu____17221 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____17221 "");
                          (let uu____17225 = FStar_List.tl stack  in
                           let uu____17226 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____17225 uu____17226)
                           in
                        let uu____17231 =
                          let uu____17232 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____17232.FStar_Syntax_Syntax.n  in
                        match uu____17231 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____17238 =
                              let uu____17240 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____17240  in
                            if uu____17238
                            then fallback1 ()
                            else
                              (let uu____17245 =
                                 let uu____17247 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____17247  in
                               if uu____17245
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____17264 =
                                      let uu____17269 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____17269 args
                                       in
                                    uu____17264 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____17270 = FStar_List.tl stack  in
                                  norm cfg env uu____17270 t1))
                        | uu____17271 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____17273) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____17297 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____17297  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____17301  ->
                            let uu____17302 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____17302);
                       (let uu____17305 = FStar_List.tl stack  in
                        norm cfg env uu____17305 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____17426  ->
                                match uu____17426 with
                                | (pat,wopt,tm) ->
                                    let uu____17474 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____17474)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____17506 = FStar_List.tl stack  in
                      norm cfg env uu____17506 tm
                  | uu____17507 -> fallback ()))

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
              (fun uu____17521  ->
                 let uu____17522 = FStar_Ident.string_of_lid msrc  in
                 let uu____17524 = FStar_Ident.string_of_lid mtgt  in
                 let uu____17526 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____17522
                   uu____17524 uu____17526);
            (let uu____17529 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____17532 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env)
                     in
                  Prims.op_Negation uu____17532)
                in
             if uu____17529
             then
               let ed =
                 let uu____17537 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____17537  in
               let uu____17538 =
                 let uu____17545 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr
                    in
                 FStar_All.pipe_right uu____17545 FStar_Util.must  in
               match uu____17538 with
               | (uu____17582,return_repr) ->
                   let return_inst =
                     let uu____17591 =
                       let uu____17592 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____17592.FStar_Syntax_Syntax.n  in
                     match uu____17591 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____17598::[]) ->
                         let uu____17603 =
                           let uu____17610 =
                             let uu____17611 =
                               let uu____17618 =
                                 let uu____17619 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____17619]  in
                               (return_tm, uu____17618)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____17611  in
                           FStar_Syntax_Syntax.mk uu____17610  in
                         uu____17603 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____17622 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____17626 =
                     let uu____17633 =
                       let uu____17634 =
                         let uu____17651 =
                           let uu____17662 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____17671 =
                             let uu____17682 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____17682]  in
                           uu____17662 :: uu____17671  in
                         (return_inst, uu____17651)  in
                       FStar_Syntax_Syntax.Tm_app uu____17634  in
                     FStar_Syntax_Syntax.mk uu____17633  in
                   uu____17626 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____17729 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____17729 with
                | FStar_Pervasives_Native.None  ->
                    let uu____17732 =
                      let uu____17734 = FStar_Ident.text_of_lid msrc  in
                      let uu____17736 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____17734 uu____17736
                       in
                    failwith uu____17732
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17739;
                      FStar_TypeChecker_Env.mtarget = uu____17740;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17741;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____17761 =
                      let uu____17763 = FStar_Ident.text_of_lid msrc  in
                      let uu____17765 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____17763 uu____17765
                       in
                    failwith uu____17761
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____17768;
                      FStar_TypeChecker_Env.mtarget = uu____17769;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____17770;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____17801 =
                        FStar_TypeChecker_Env.is_reifiable_effect env msrc
                         in
                      if uu____17801
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____17806 =
                           let uu____17813 =
                             let uu____17814 =
                               let uu____17833 =
                                 let uu____17842 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____17842]  in
                               (uu____17833, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____17814  in
                           FStar_Syntax_Syntax.mk uu____17813  in
                         uu____17806 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____17875 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    lift uu____17875 t e1))

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
                (fun uu____17945  ->
                   match uu____17945 with
                   | (a,imp) ->
                       let uu____17964 = norm cfg env [] a  in
                       (uu____17964, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17974  ->
             let uu____17975 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17977 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17975 uu____17977);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____18003 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _18006  -> FStar_Pervasives_Native.Some _18006)
                     uu____18003
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2239_18007 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2239_18007.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2239_18007.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____18029 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _18032  -> FStar_Pervasives_Native.Some _18032)
                     uu____18029
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2250_18033 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2250_18033.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2250_18033.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____18078  ->
                      match uu____18078 with
                      | (a,i) ->
                          let uu____18098 = norm cfg env [] a  in
                          (uu____18098, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_18120  ->
                       match uu___14_18120 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____18124 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____18124
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2267_18132 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2269_18135 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2269_18135.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2267_18132.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2267_18132.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____18139 = b  in
        match uu____18139 with
        | (x,imp) ->
            let x1 =
              let uu___2277_18147 = x  in
              let uu____18148 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2277_18147.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2277_18147.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____18148
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____18159 =
                    let uu____18160 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____18160  in
                  FStar_Pervasives_Native.Some uu____18159
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____18171 =
          FStar_List.fold_left
            (fun uu____18205  ->
               fun b  ->
                 match uu____18205 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____18171 with | (nbs,uu____18285) -> FStar_List.rev nbs

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
            let uu____18317 =
              let uu___2302_18318 = rc  in
              let uu____18319 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2302_18318.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____18319;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2302_18318.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____18317
        | uu____18337 -> lopt

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
            (let uu____18347 = FStar_Syntax_Print.term_to_string tm  in
             let uu____18349 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____18347 uu____18349)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_18361  ->
      match uu___15_18361 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____18374 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____18374 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____18378 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____18378)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____18386 = norm_cb cfg  in
            reduce_primops uu____18386 cfg env tm  in
          let uu____18391 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____18391
          then tm1
          else
            (let w t =
               let uu___2331_18410 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2331_18410.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2331_18410.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____18422 =
                 let uu____18423 = FStar_Syntax_Util.unmeta t  in
                 uu____18423.FStar_Syntax_Syntax.n  in
               match uu____18422 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____18435 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____18499)::args1,(bv,uu____18502)::bs1) ->
                   let uu____18556 =
                     let uu____18557 = FStar_Syntax_Subst.compress t  in
                     uu____18557.FStar_Syntax_Syntax.n  in
                   (match uu____18556 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____18562 -> false)
               | ([],[]) -> true
               | (uu____18593,uu____18594) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18645 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18647 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____18645
                    uu____18647)
               else ();
               (let uu____18652 = FStar_Syntax_Util.head_and_args' t  in
                match uu____18652 with
                | (hd1,args) ->
                    let uu____18691 =
                      let uu____18692 = FStar_Syntax_Subst.compress hd1  in
                      uu____18692.FStar_Syntax_Syntax.n  in
                    (match uu____18691 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____18700 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____18702 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____18704 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____18700 uu____18702 uu____18704)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____18709 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____18727 = FStar_Syntax_Print.term_to_string t  in
                  let uu____18729 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____18727
                    uu____18729)
               else ();
               (let uu____18734 = FStar_Syntax_Util.is_squash t  in
                match uu____18734 with
                | FStar_Pervasives_Native.Some (uu____18745,t') ->
                    is_applied bs t'
                | uu____18757 ->
                    let uu____18766 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____18766 with
                     | FStar_Pervasives_Native.Some (uu____18777,t') ->
                         is_applied bs t'
                     | uu____18789 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____18813 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18813 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____18820)::(q,uu____18822)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18865 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____18867 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____18865 uu____18867)
                    else ();
                    (let uu____18872 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____18872 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____18877 =
                           let uu____18878 = FStar_Syntax_Subst.compress p
                              in
                           uu____18878.FStar_Syntax_Syntax.n  in
                         (match uu____18877 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____18889 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18889))
                          | uu____18892 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____18895)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____18920 =
                           let uu____18921 = FStar_Syntax_Subst.compress p1
                              in
                           uu____18921.FStar_Syntax_Syntax.n  in
                         (match uu____18920 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____18932 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____18932))
                          | uu____18935 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____18939 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____18939 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____18944 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____18944 with
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
                                     let uu____18958 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18958))
                               | uu____18961 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____18966)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18991 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18991 with
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
                                     let uu____19005 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____19005))
                               | uu____19008 -> FStar_Pervasives_Native.None)
                          | uu____19011 -> FStar_Pervasives_Native.None)
                     | uu____19014 -> FStar_Pervasives_Native.None))
               | uu____19017 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____19030 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____19030 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____19036)::[],uu____19037,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____19057 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____19059 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____19057
                         uu____19059)
                    else ();
                    is_quantified_const bv phi')
               | uu____19064 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____19079 =
                 let uu____19080 = FStar_Syntax_Subst.compress phi  in
                 uu____19080.FStar_Syntax_Syntax.n  in
               match uu____19079 with
               | FStar_Syntax_Syntax.Tm_match (uu____19086,br::brs) ->
                   let uu____19153 = br  in
                   (match uu____19153 with
                    | (uu____19171,uu____19172,e) ->
                        let r =
                          let uu____19194 = simp_t e  in
                          match uu____19194 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____19206 =
                                FStar_List.for_all
                                  (fun uu____19225  ->
                                     match uu____19225 with
                                     | (uu____19239,uu____19240,e') ->
                                         let uu____19254 = simp_t e'  in
                                         uu____19254 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____19206
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____19270 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____19280 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____19280
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____19318 =
                 match uu____19318 with
                 | (t1,q) ->
                     let uu____19339 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____19339 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____19371 -> (t1, q))
                  in
               let uu____19384 = FStar_Syntax_Util.head_and_args t  in
               match uu____19384 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____19464 =
                 let uu____19465 = FStar_Syntax_Util.unmeta ty  in
                 uu____19465.FStar_Syntax_Syntax.n  in
               match uu____19464 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____19470) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____19475,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____19499 -> false  in
             let simplify1 arg =
               let uu____19532 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____19532, arg)  in
             let uu____19547 = is_forall_const tm1  in
             match uu____19547 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____19553 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____19555 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____19553
                       uu____19555)
                  else ();
                  (let uu____19560 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____19560))
             | FStar_Pervasives_Native.None  ->
                 let uu____19561 =
                   let uu____19562 = FStar_Syntax_Subst.compress tm1  in
                   uu____19562.FStar_Syntax_Syntax.n  in
                 (match uu____19561 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____19566;
                              FStar_Syntax_Syntax.vars = uu____19567;_},uu____19568);
                         FStar_Syntax_Syntax.pos = uu____19569;
                         FStar_Syntax_Syntax.vars = uu____19570;_},args)
                      ->
                      let uu____19600 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____19600
                      then
                        let uu____19603 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____19603 with
                         | (FStar_Pervasives_Native.Some (true ),uu____19661)::
                             (uu____19662,(arg,uu____19664))::[] ->
                             maybe_auto_squash arg
                         | (uu____19737,(arg,uu____19739))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____19740)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____19813)::uu____19814::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____19884::(FStar_Pervasives_Native.Some (false
                                         ),uu____19885)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____19955 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____19973 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____19973
                         then
                           let uu____19976 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____19976 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20034)::uu____20035::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20105::(FStar_Pervasives_Native.Some (true
                                           ),uu____20106)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20176)::(uu____20177,(arg,uu____20179))::[]
                               -> maybe_auto_squash arg
                           | (uu____20252,(arg,uu____20254))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20255)::[]
                               -> maybe_auto_squash arg
                           | uu____20328 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20346 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20346
                            then
                              let uu____20349 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20349 with
                              | uu____20407::(FStar_Pervasives_Native.Some
                                              (true ),uu____20408)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____20478)::uu____20479::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____20549)::(uu____20550,(arg,uu____20552))::[]
                                  -> maybe_auto_squash arg
                              | (uu____20625,(p,uu____20627))::(uu____20628,
                                                                (q,uu____20630))::[]
                                  ->
                                  let uu____20702 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____20702
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____20707 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____20725 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____20725
                               then
                                 let uu____20728 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____20728 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20786)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20787)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20861)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20862)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20936)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____20937)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21011)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21012)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21086,(arg,uu____21088))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21089)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21162)::(uu____21163,(arg,uu____21165))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21238,(arg,uu____21240))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21241)::[]
                                     ->
                                     let uu____21314 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21314
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21315)::(uu____21316,(arg,uu____21318))::[]
                                     ->
                                     let uu____21391 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21391
                                 | (uu____21392,(p,uu____21394))::(uu____21395,
                                                                   (q,uu____21397))::[]
                                     ->
                                     let uu____21469 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____21469
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____21474 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____21492 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____21492
                                  then
                                    let uu____21495 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____21495 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____21553)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____21597)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____21641 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____21659 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____21659
                                     then
                                       match args with
                                       | (t,uu____21663)::[] ->
                                           let uu____21688 =
                                             let uu____21689 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21689.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21688 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21692::[],body,uu____21694)
                                                ->
                                                let uu____21729 = simp_t body
                                                   in
                                                (match uu____21729 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____21735 -> tm1)
                                            | uu____21739 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____21741))::(t,uu____21743)::[]
                                           ->
                                           let uu____21783 =
                                             let uu____21784 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____21784.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____21783 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____21787::[],body,uu____21789)
                                                ->
                                                let uu____21824 = simp_t body
                                                   in
                                                (match uu____21824 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____21832 -> tm1)
                                            | uu____21836 -> tm1)
                                       | uu____21837 -> tm1
                                     else
                                       (let uu____21850 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____21850
                                        then
                                          match args with
                                          | (t,uu____21854)::[] ->
                                              let uu____21879 =
                                                let uu____21880 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21880.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21879 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21883::[],body,uu____21885)
                                                   ->
                                                   let uu____21920 =
                                                     simp_t body  in
                                                   (match uu____21920 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____21926 -> tm1)
                                               | uu____21930 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____21932))::(t,uu____21934)::[]
                                              ->
                                              let uu____21974 =
                                                let uu____21975 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____21975.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____21974 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21978::[],body,uu____21980)
                                                   ->
                                                   let uu____22015 =
                                                     simp_t body  in
                                                   (match uu____22015 with
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
                                                    | uu____22023 -> tm1)
                                               | uu____22027 -> tm1)
                                          | uu____22028 -> tm1
                                        else
                                          (let uu____22041 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22041
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22044;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22045;_},uu____22046)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22072;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22073;_},uu____22074)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22100 -> tm1
                                           else
                                             (let uu____22113 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____22113
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____22127 =
                                                    let uu____22128 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____22128.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____22127 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____22139 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____22153 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____22153
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____22192 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____22192
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____22198 =
                                                         let uu____22199 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____22199.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____22198 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____22202 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____22210 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____22210
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____22219
                                                                  =
                                                                  let uu____22220
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____22220.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____22219
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____22226)
                                                                    -> hd1
                                                                | uu____22251
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____22255
                                                                =
                                                                let uu____22266
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____22266]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____22255)
                                                       | uu____22299 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____22304 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____22304 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____22324 ->
                                                     let uu____22333 =
                                                       let uu____22340 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____22340 cfg env
                                                        in
                                                     uu____22333 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____22346;
                         FStar_Syntax_Syntax.vars = uu____22347;_},args)
                      ->
                      let uu____22373 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____22373
                      then
                        let uu____22376 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____22376 with
                         | (FStar_Pervasives_Native.Some (true ),uu____22434)::
                             (uu____22435,(arg,uu____22437))::[] ->
                             maybe_auto_squash arg
                         | (uu____22510,(arg,uu____22512))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____22513)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____22586)::uu____22587::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____22657::(FStar_Pervasives_Native.Some (false
                                         ),uu____22658)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____22728 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____22746 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____22746
                         then
                           let uu____22749 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____22749 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____22807)::uu____22808::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____22878::(FStar_Pervasives_Native.Some (true
                                           ),uu____22879)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____22949)::(uu____22950,(arg,uu____22952))::[]
                               -> maybe_auto_squash arg
                           | (uu____23025,(arg,uu____23027))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____23028)::[]
                               -> maybe_auto_squash arg
                           | uu____23101 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____23119 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____23119
                            then
                              let uu____23122 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____23122 with
                              | uu____23180::(FStar_Pervasives_Native.Some
                                              (true ),uu____23181)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____23251)::uu____23252::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____23322)::(uu____23323,(arg,uu____23325))::[]
                                  -> maybe_auto_squash arg
                              | (uu____23398,(p,uu____23400))::(uu____23401,
                                                                (q,uu____23403))::[]
                                  ->
                                  let uu____23475 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____23475
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____23480 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____23498 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____23498
                               then
                                 let uu____23501 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____23501 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23559)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23560)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23634)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23635)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23709)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____23710)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23784)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____23785)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____23859,(arg,uu____23861))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____23862)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____23935)::(uu____23936,(arg,uu____23938))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____24011,(arg,uu____24013))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____24014)::[]
                                     ->
                                     let uu____24087 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____24087
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____24088)::(uu____24089,(arg,uu____24091))::[]
                                     ->
                                     let uu____24164 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____24164
                                 | (uu____24165,(p,uu____24167))::(uu____24168,
                                                                   (q,uu____24170))::[]
                                     ->
                                     let uu____24242 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____24242
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____24247 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____24265 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____24265
                                  then
                                    let uu____24268 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____24268 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____24326)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____24370)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____24414 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____24432 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____24432
                                     then
                                       match args with
                                       | (t,uu____24436)::[] ->
                                           let uu____24461 =
                                             let uu____24462 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24462.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24461 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24465::[],body,uu____24467)
                                                ->
                                                let uu____24502 = simp_t body
                                                   in
                                                (match uu____24502 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____24508 -> tm1)
                                            | uu____24512 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____24514))::(t,uu____24516)::[]
                                           ->
                                           let uu____24556 =
                                             let uu____24557 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____24557.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____24556 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____24560::[],body,uu____24562)
                                                ->
                                                let uu____24597 = simp_t body
                                                   in
                                                (match uu____24597 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____24605 -> tm1)
                                            | uu____24609 -> tm1)
                                       | uu____24610 -> tm1
                                     else
                                       (let uu____24623 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____24623
                                        then
                                          match args with
                                          | (t,uu____24627)::[] ->
                                              let uu____24652 =
                                                let uu____24653 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24653.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24652 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24656::[],body,uu____24658)
                                                   ->
                                                   let uu____24693 =
                                                     simp_t body  in
                                                   (match uu____24693 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____24699 -> tm1)
                                               | uu____24703 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____24705))::(t,uu____24707)::[]
                                              ->
                                              let uu____24747 =
                                                let uu____24748 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____24748.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____24747 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____24751::[],body,uu____24753)
                                                   ->
                                                   let uu____24788 =
                                                     simp_t body  in
                                                   (match uu____24788 with
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
                                                    | uu____24796 -> tm1)
                                               | uu____24800 -> tm1)
                                          | uu____24801 -> tm1
                                        else
                                          (let uu____24814 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____24814
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24817;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24818;_},uu____24819)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____24845;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____24846;_},uu____24847)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____24873 -> tm1
                                           else
                                             (let uu____24886 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____24886
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____24900 =
                                                    let uu____24901 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____24901.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____24900 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____24912 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____24926 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____24926
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____24961 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____24961
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____24967 =
                                                         let uu____24968 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____24968.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____24967 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____24971 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24979 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24979
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24988
                                                                  =
                                                                  let uu____24989
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24989.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24988
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____24995)
                                                                    -> hd1
                                                                | uu____25020
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____25024
                                                                =
                                                                let uu____25035
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____25035]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____25024)
                                                       | uu____25068 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____25073 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____25073 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____25093 ->
                                                     let uu____25102 =
                                                       let uu____25109 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____25109 cfg env
                                                        in
                                                     uu____25102 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____25120 = simp_t t  in
                      (match uu____25120 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____25129 ->
                      let uu____25152 = is_const_match tm1  in
                      (match uu____25152 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____25161 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____25171  ->
               (let uu____25173 = FStar_Syntax_Print.tag_of_term t  in
                let uu____25175 = FStar_Syntax_Print.term_to_string t  in
                let uu____25177 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____25185 =
                  let uu____25187 =
                    let uu____25190 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____25190
                     in
                  stack_to_string uu____25187  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____25173 uu____25175 uu____25177 uu____25185);
               (let uu____25215 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____25215
                then
                  let uu____25219 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____25219 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____25226 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____25228 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____25230 =
                          let uu____25232 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____25232
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____25226
                          uu____25228 uu____25230);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____25254 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____25262)::uu____25263 -> true
                | uu____25273 -> false)
              in
           if uu____25254
           then
             let uu____25276 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____25276 (norm cfg env stack)
           else
             (let t_opt = is_wp_req_ens_commutation cfg t  in
              let uu____25284 = FStar_All.pipe_right t_opt FStar_Util.is_some
                 in
              if uu____25284
              then
                ((let uu____25291 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         cfg.FStar_TypeChecker_Cfg.tcenv)
                      (FStar_Options.Other "WPReqEns")
                     in
                  if uu____25291
                  then
                    let uu____25296 = FStar_Syntax_Print.term_to_string t  in
                    let uu____25298 =
                      let uu____25300 =
                        FStar_All.pipe_right t_opt FStar_Util.must  in
                      FStar_All.pipe_right uu____25300
                        FStar_Syntax_Print.term_to_string
                       in
                    FStar_Util.print2
                      "In rebuild: reduced a wp req ens commutation from \n%s\n to \n%s"
                      uu____25296 uu____25298
                  else ());
                 (let uu____25307 =
                    FStar_All.pipe_right t_opt FStar_Util.must  in
                  FStar_All.pipe_right uu____25307 (norm cfg env stack)))
              else
                (let t1 = maybe_simplify cfg env stack t  in
                 match stack with
                 | [] -> t1
                 | (Debug (tm,time_then))::stack1 ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let time_now = FStar_Util.now ()  in
                         let uu____25321 =
                           let uu____25323 =
                             let uu____25325 =
                               FStar_Util.time_diff time_then time_now  in
                             FStar_Pervasives_Native.snd uu____25325  in
                           FStar_Util.string_of_int uu____25323  in
                         let uu____25332 =
                           FStar_Syntax_Print.term_to_string tm  in
                         let uu____25334 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                         let uu____25336 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print4
                           "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____25321 uu____25332 uu____25334 uu____25336)
                      else ();
                      rebuild cfg env stack1 t1)
                 | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
                 | (Meta (uu____25345,m,r))::stack1 ->
                     let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                     rebuild cfg env stack1 t2
                 | (MemoLazy r)::stack1 ->
                     (set_memo cfg r (env, t1);
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____25374  ->
                           let uu____25375 =
                             FStar_Syntax_Print.term_to_string t1  in
                           FStar_Util.print1 "\tSet memo %s\n" uu____25375);
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
                     let uu____25418 =
                       let uu___2964_25419 =
                         FStar_Syntax_Util.abs bs1 t1 lopt1  in
                       {
                         FStar_Syntax_Syntax.n =
                           (uu___2964_25419.FStar_Syntax_Syntax.n);
                         FStar_Syntax_Syntax.pos = r;
                         FStar_Syntax_Syntax.vars =
                           (uu___2964_25419.FStar_Syntax_Syntax.vars)
                       }  in
                     rebuild cfg env stack1 uu____25418
                 | (Arg
                     (Univ uu____25422,uu____25423,uu____25424))::uu____25425
                     -> failwith "Impossible"
                 | (Arg (Dummy ,uu____25429,uu____25430))::uu____25431 ->
                     failwith "Impossible"
                 | (UnivArgs (us,r))::stack1 ->
                     let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                     rebuild cfg env stack1 t2
                 | (Arg
                     (Clos (env_arg,tm,uu____25447,uu____25448),aq,r))::stack1
                     when
                     let uu____25500 = head_of t1  in
                     FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____25500
                     ->
                     let t2 =
                       let uu____25504 =
                         let uu____25509 =
                           let uu____25510 = closure_as_term cfg env_arg tm
                              in
                           (uu____25510, aq)  in
                         FStar_Syntax_Syntax.extend_app t1 uu____25509  in
                       uu____25504 FStar_Pervasives_Native.None r  in
                     rebuild cfg env stack1 t2
                 | (Arg (Clos (env_arg,tm,m,uu____25520),aq,r))::stack1 ->
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____25575  ->
                           let uu____25576 =
                             FStar_Syntax_Print.term_to_string tm  in
                           FStar_Util.print1 "Rebuilding with arg %s\n"
                             uu____25576);
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
                        (let uu____25596 = FStar_ST.op_Bang m  in
                         match uu____25596 with
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
                         | FStar_Pervasives_Native.Some (uu____25684,a) ->
                             let t2 =
                               FStar_Syntax_Syntax.extend_app t1 (a, aq)
                                 FStar_Pervasives_Native.None r
                                in
                             rebuild cfg env_arg stack1 t2))
                 | (App (env1,head1,aq,r))::stack' when
                     should_reify cfg stack ->
                     let t0 = t1  in
                     let fallback msg uu____25740 =
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____25745  ->
                            let uu____25746 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not reifying%s: %s\n" msg
                              uu____25746);
                       (let t2 =
                          FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                            FStar_Pervasives_Native.None r
                           in
                        rebuild cfg env1 stack' t2)
                        in
                     let uu____25756 =
                       let uu____25757 = FStar_Syntax_Subst.compress t1  in
                       uu____25757.FStar_Syntax_Syntax.n  in
                     (match uu____25756 with
                      | FStar_Syntax_Syntax.Tm_meta
                          (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                          do_reify_monadic (fallback " (1)") cfg env1 stack
                            t2 m ty
                      | FStar_Syntax_Syntax.Tm_meta
                          (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                           (msrc,mtgt,ty))
                          ->
                          let lifted =
                            let uu____25785 = closure_as_term cfg env1 ty  in
                            reify_lift cfg t2 msrc mtgt uu____25785  in
                          (FStar_TypeChecker_Cfg.log cfg
                             (fun uu____25789  ->
                                let uu____25790 =
                                  FStar_Syntax_Print.term_to_string lifted
                                   in
                                FStar_Util.print1 "Reified lift to (1): %s\n"
                                  uu____25790);
                           (let uu____25793 = FStar_List.tl stack  in
                            norm cfg env1 uu____25793 lifted))
                      | FStar_Syntax_Syntax.Tm_app
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reflect uu____25794);
                             FStar_Syntax_Syntax.pos = uu____25795;
                             FStar_Syntax_Syntax.vars = uu____25796;_},
                           (e,uu____25798)::[])
                          -> norm cfg env1 stack' e
                      | FStar_Syntax_Syntax.Tm_app uu____25837 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                          ->
                          let uu____25854 =
                            FStar_Syntax_Util.head_and_args t1  in
                          (match uu____25854 with
                           | (hd1,args) ->
                               let uu____25897 =
                                 let uu____25898 =
                                   FStar_Syntax_Util.un_uinst hd1  in
                                 uu____25898.FStar_Syntax_Syntax.n  in
                               (match uu____25897 with
                                | FStar_Syntax_Syntax.Tm_fvar fv ->
                                    let uu____25902 =
                                      FStar_TypeChecker_Cfg.find_prim_step
                                        cfg fv
                                       in
                                    (match uu____25902 with
                                     | FStar_Pervasives_Native.Some
                                         {
                                           FStar_TypeChecker_Cfg.name =
                                             uu____25905;
                                           FStar_TypeChecker_Cfg.arity =
                                             uu____25906;
                                           FStar_TypeChecker_Cfg.univ_arity =
                                             uu____25907;
                                           FStar_TypeChecker_Cfg.auto_reflect
                                             = FStar_Pervasives_Native.Some
                                             n1;
                                           FStar_TypeChecker_Cfg.strong_reduction_ok
                                             = uu____25909;
                                           FStar_TypeChecker_Cfg.requires_binder_substitution
                                             = uu____25910;
                                           FStar_TypeChecker_Cfg.interpretation
                                             = uu____25911;
                                           FStar_TypeChecker_Cfg.interpretation_nbe
                                             = uu____25912;_}
                                         when (FStar_List.length args) = n1
                                         -> norm cfg env1 stack' t1
                                     | uu____25948 -> fallback " (3)" ())
                                | uu____25952 -> fallback " (4)" ()))
                      | uu____25954 -> fallback " (2)" ())
                 | (App (env1,head1,aq,r))::stack1 ->
                     let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack1 t2
                 | (Match (env',branches,cfg1,r))::stack1 ->
                     (FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____25980  ->
                           let uu____25981 =
                             FStar_Syntax_Print.term_to_string t1  in
                           FStar_Util.print1
                             "Rebuilding with match, scrutinee is %s ...\n"
                             uu____25981);
                      (let scrutinee_env = env  in
                       let env1 = env'  in
                       let scrutinee = t1  in
                       let norm_and_rebuild_match uu____25992 =
                         FStar_TypeChecker_Cfg.log cfg1
                           (fun uu____25997  ->
                              let uu____25998 =
                                FStar_Syntax_Print.term_to_string scrutinee
                                 in
                              let uu____26000 =
                                let uu____26002 =
                                  FStar_All.pipe_right branches
                                    (FStar_List.map
                                       (fun uu____26032  ->
                                          match uu____26032 with
                                          | (p,uu____26043,uu____26044) ->
                                              FStar_Syntax_Print.pat_to_string
                                                p))
                                   in
                                FStar_All.pipe_right uu____26002
                                  (FStar_String.concat "\n\t")
                                 in
                              FStar_Util.print2
                                "match is irreducible: scrutinee=%s\nbranches=%s\n"
                                uu____25998 uu____26000);
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
                                   (fun uu___16_26066  ->
                                      match uu___16_26066 with
                                      | FStar_TypeChecker_Env.InliningDelta 
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                           -> true
                                      | uu____26070 -> false))
                               in
                            let steps =
                              let uu___3132_26073 =
                                cfg1.FStar_TypeChecker_Cfg.steps  in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3132_26073.FStar_TypeChecker_Cfg.for_extraction)
                              }  in
                            let uu___3135_26080 = cfg1  in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3135_26080.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3135_26080.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3135_26080.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3135_26080.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3135_26080.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3135_26080.FStar_TypeChecker_Cfg.reifying)
                            }  in
                          let norm_or_whnf env2 t2 =
                            if whnf
                            then closure_as_term cfg_exclude_zeta env2 t2
                            else norm cfg_exclude_zeta env2 [] t2  in
                          let rec norm_pat env2 p =
                            match p.FStar_Syntax_Syntax.v with
                            | FStar_Syntax_Syntax.Pat_constant uu____26155 ->
                                (p, env2)
                            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                                let uu____26186 =
                                  FStar_All.pipe_right pats
                                    (FStar_List.fold_left
                                       (fun uu____26275  ->
                                          fun uu____26276  ->
                                            match (uu____26275, uu____26276)
                                            with
                                            | ((pats1,env3),(p1,b)) ->
                                                let uu____26426 =
                                                  norm_pat env3 p1  in
                                                (match uu____26426 with
                                                 | (p2,env4) ->
                                                     (((p2, b) :: pats1),
                                                       env4))) ([], env2))
                                   in
                                (match uu____26186 with
                                 | (pats1,env3) ->
                                     ((let uu___3163_26596 = p  in
                                       {
                                         FStar_Syntax_Syntax.v =
                                           (FStar_Syntax_Syntax.Pat_cons
                                              (fv, (FStar_List.rev pats1)));
                                         FStar_Syntax_Syntax.p =
                                           (uu___3163_26596.FStar_Syntax_Syntax.p)
                                       }), env3))
                            | FStar_Syntax_Syntax.Pat_var x ->
                                let x1 =
                                  let uu___3167_26617 = x  in
                                  let uu____26618 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3167_26617.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3167_26617.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26618
                                  }  in
                                ((let uu___3170_26632 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_var x1);
                                    FStar_Syntax_Syntax.p =
                                      (uu___3170_26632.FStar_Syntax_Syntax.p)
                                  }), (dummy :: env2))
                            | FStar_Syntax_Syntax.Pat_wild x ->
                                let x1 =
                                  let uu___3174_26643 = x  in
                                  let uu____26644 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3174_26643.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3174_26643.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26644
                                  }  in
                                ((let uu___3177_26658 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_wild x1);
                                    FStar_Syntax_Syntax.p =
                                      (uu___3177_26658.FStar_Syntax_Syntax.p)
                                  }), (dummy :: env2))
                            | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                                let x1 =
                                  let uu___3183_26674 = x  in
                                  let uu____26675 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3183_26674.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3183_26674.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26675
                                  }  in
                                let t3 = norm_or_whnf env2 t2  in
                                ((let uu___3187_26690 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_dot_term
                                         (x1, t3));
                                    FStar_Syntax_Syntax.p =
                                      (uu___3187_26690.FStar_Syntax_Syntax.p)
                                  }), env2)
                             in
                          let branches1 =
                            match env1 with
                            | [] when whnf -> branches
                            | uu____26734 ->
                                FStar_All.pipe_right branches
                                  (FStar_List.map
                                     (fun branch1  ->
                                        let uu____26764 =
                                          FStar_Syntax_Subst.open_branch
                                            branch1
                                           in
                                        match uu____26764 with
                                        | (p,wopt,e) ->
                                            let uu____26784 = norm_pat env1 p
                                               in
                                            (match uu____26784 with
                                             | (p1,env2) ->
                                                 let wopt1 =
                                                   match wopt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       FStar_Pervasives_Native.None
                                                   | FStar_Pervasives_Native.Some
                                                       w ->
                                                       let uu____26839 =
                                                         norm_or_whnf env2 w
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____26839
                                                    in
                                                 let e1 = norm_or_whnf env2 e
                                                    in
                                                 FStar_Syntax_Util.branch
                                                   (p1, wopt1, e1))))
                             in
                          let scrutinee1 =
                            let uu____26856 =
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
                            if uu____26856
                            then
                              norm
                                (let uu___3206_26863 = cfg1  in
                                 {
                                   FStar_TypeChecker_Cfg.steps =
                                     (let uu___3208_26866 =
                                        cfg1.FStar_TypeChecker_Cfg.steps  in
                                      {
                                        FStar_TypeChecker_Cfg.beta =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.beta);
                                        FStar_TypeChecker_Cfg.iota =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.iota);
                                        FStar_TypeChecker_Cfg.zeta =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.zeta);
                                        FStar_TypeChecker_Cfg.weak =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.weak);
                                        FStar_TypeChecker_Cfg.hnf =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.hnf);
                                        FStar_TypeChecker_Cfg.primops =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.primops);
                                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                          =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                        FStar_TypeChecker_Cfg.unfold_until =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.unfold_until);
                                        FStar_TypeChecker_Cfg.unfold_only =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.unfold_only);
                                        FStar_TypeChecker_Cfg.unfold_fully =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.unfold_fully);
                                        FStar_TypeChecker_Cfg.unfold_attr =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.unfold_attr);
                                        FStar_TypeChecker_Cfg.unfold_tac =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.unfold_tac);
                                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                          =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                        FStar_TypeChecker_Cfg.simplify =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.simplify);
                                        FStar_TypeChecker_Cfg.erase_universes
                                          =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.erase_universes);
                                        FStar_TypeChecker_Cfg.allow_unbound_universes
                                          =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                        FStar_TypeChecker_Cfg.reify_ =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.reify_);
                                        FStar_TypeChecker_Cfg.compress_uvars
                                          =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.compress_uvars);
                                        FStar_TypeChecker_Cfg.no_full_norm =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.no_full_norm);
                                        FStar_TypeChecker_Cfg.check_no_uvars
                                          =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.check_no_uvars);
                                        FStar_TypeChecker_Cfg.unmeta =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.unmeta);
                                        FStar_TypeChecker_Cfg.unascribe =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.unascribe);
                                        FStar_TypeChecker_Cfg.in_full_norm_request
                                          =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.in_full_norm_request);
                                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                          = false;
                                        FStar_TypeChecker_Cfg.nbe_step =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.nbe_step);
                                        FStar_TypeChecker_Cfg.for_extraction
                                          =
                                          (uu___3208_26866.FStar_TypeChecker_Cfg.for_extraction)
                                      });
                                   FStar_TypeChecker_Cfg.tcenv =
                                     (uu___3206_26863.FStar_TypeChecker_Cfg.tcenv);
                                   FStar_TypeChecker_Cfg.debug =
                                     (uu___3206_26863.FStar_TypeChecker_Cfg.debug);
                                   FStar_TypeChecker_Cfg.delta_level =
                                     (uu___3206_26863.FStar_TypeChecker_Cfg.delta_level);
                                   FStar_TypeChecker_Cfg.primitive_steps =
                                     (uu___3206_26863.FStar_TypeChecker_Cfg.primitive_steps);
                                   FStar_TypeChecker_Cfg.strong =
                                     (uu___3206_26863.FStar_TypeChecker_Cfg.strong);
                                   FStar_TypeChecker_Cfg.memoize_lazy =
                                     (uu___3206_26863.FStar_TypeChecker_Cfg.memoize_lazy);
                                   FStar_TypeChecker_Cfg.normalize_pure_lets
                                     =
                                     (uu___3206_26863.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                   FStar_TypeChecker_Cfg.reifying =
                                     (uu___3206_26863.FStar_TypeChecker_Cfg.reifying)
                                 }) scrutinee_env [] scrutinee
                            else scrutinee  in
                          let uu____26870 =
                            mk
                              (FStar_Syntax_Syntax.Tm_match
                                 (scrutinee1, branches1)) r
                             in
                          rebuild cfg1 env1 stack1 uu____26870)
                          in
                       let rec is_cons head1 =
                         let uu____26896 =
                           let uu____26897 =
                             FStar_Syntax_Subst.compress head1  in
                           uu____26897.FStar_Syntax_Syntax.n  in
                         match uu____26896 with
                         | FStar_Syntax_Syntax.Tm_uinst (h,uu____26902) ->
                             is_cons h
                         | FStar_Syntax_Syntax.Tm_constant uu____26907 ->
                             true
                         | FStar_Syntax_Syntax.Tm_fvar
                             { FStar_Syntax_Syntax.fv_name = uu____26909;
                               FStar_Syntax_Syntax.fv_delta = uu____26910;
                               FStar_Syntax_Syntax.fv_qual =
                                 FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Data_ctor );_}
                             -> true
                         | FStar_Syntax_Syntax.Tm_fvar
                             { FStar_Syntax_Syntax.fv_name = uu____26912;
                               FStar_Syntax_Syntax.fv_delta = uu____26913;
                               FStar_Syntax_Syntax.fv_qual =
                                 FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Record_ctor
                                 uu____26914);_}
                             -> true
                         | uu____26922 -> false  in
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
                         let uu____27091 =
                           FStar_Syntax_Util.head_and_args scrutinee2  in
                         match uu____27091 with
                         | (head1,args) ->
                             (match p.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_var bv ->
                                  FStar_Util.Inl [(bv, scrutinee_orig)]
                              | FStar_Syntax_Syntax.Pat_wild bv ->
                                  FStar_Util.Inl [(bv, scrutinee_orig)]
                              | FStar_Syntax_Syntax.Pat_dot_term uu____27188
                                  -> FStar_Util.Inl []
                              | FStar_Syntax_Syntax.Pat_constant s ->
                                  (match scrutinee2.FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_constant s' when
                                       FStar_Const.eq_const s s' ->
                                       FStar_Util.Inl []
                                   | uu____27230 ->
                                       let uu____27231 =
                                         let uu____27233 = is_cons head1  in
                                         Prims.op_Negation uu____27233  in
                                       FStar_Util.Inr uu____27231)
                              | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                                  let uu____27262 =
                                    let uu____27263 =
                                      FStar_Syntax_Util.un_uinst head1  in
                                    uu____27263.FStar_Syntax_Syntax.n  in
                                  (match uu____27262 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv' when
                                       FStar_Syntax_Syntax.fv_eq fv fv' ->
                                       matches_args [] args arg_pats
                                   | uu____27282 ->
                                       let uu____27283 =
                                         let uu____27285 = is_cons head1  in
                                         Prims.op_Negation uu____27285  in
                                       FStar_Util.Inr uu____27283))
                       
                       and matches_args out a p =
                         match (a, p) with
                         | ([],[]) -> FStar_Util.Inl out
                         | ((t2,uu____27376)::rest_a,(p1,uu____27379)::rest_p)
                             ->
                             let uu____27438 = matches_pat t2 p1  in
                             (match uu____27438 with
                              | FStar_Util.Inl s ->
                                  matches_args (FStar_List.append out s)
                                    rest_a rest_p
                              | m -> m)
                         | uu____27491 -> FStar_Util.Inr false
                        in
                       let rec matches scrutinee1 p =
                         match p with
                         | [] -> norm_and_rebuild_match ()
                         | (p1,wopt,b)::rest ->
                             let uu____27614 = matches_pat scrutinee1 p1  in
                             (match uu____27614 with
                              | FStar_Util.Inr (false ) ->
                                  matches scrutinee1 rest
                              | FStar_Util.Inr (true ) ->
                                  norm_and_rebuild_match ()
                              | FStar_Util.Inl s ->
                                  (FStar_TypeChecker_Cfg.log cfg1
                                     (fun uu____27660  ->
                                        let uu____27661 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        let uu____27663 =
                                          let uu____27665 =
                                            FStar_List.map
                                              (fun uu____27677  ->
                                                 match uu____27677 with
                                                 | (uu____27683,t2) ->
                                                     FStar_Syntax_Print.term_to_string
                                                       t2) s
                                             in
                                          FStar_All.pipe_right uu____27665
                                            (FStar_String.concat "; ")
                                           in
                                        FStar_Util.print2
                                          "Matches pattern %s with subst = %s\n"
                                          uu____27661 uu____27663);
                                   (let env0 = env1  in
                                    let env2 =
                                      FStar_List.fold_left
                                        (fun env2  ->
                                           fun uu____27719  ->
                                             match uu____27719 with
                                             | (bv,t2) ->
                                                 let uu____27742 =
                                                   let uu____27749 =
                                                     let uu____27752 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         bv
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____27752
                                                      in
                                                   let uu____27753 =
                                                     let uu____27754 =
                                                       let uu____27786 =
                                                         FStar_Util.mk_ref
                                                           (FStar_Pervasives_Native.Some
                                                              ([], t2))
                                                          in
                                                       ([], t2, uu____27786,
                                                         false)
                                                        in
                                                     Clos uu____27754  in
                                                   (uu____27749, uu____27753)
                                                    in
                                                 uu____27742 :: env2) env1 s
                                       in
                                    let uu____27879 =
                                      guard_when_clause wopt b rest  in
                                    norm cfg1 env2 stack1 uu____27879)))
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
            (fun uu____27912  ->
               let uu____27913 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____27913);
          (let uu____27916 = is_nbe_request s  in
           if uu____27916
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27922  ->
                   let uu____27923 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____27923);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27929  ->
                   let uu____27930 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27930);
              (let uu____27933 =
                 FStar_Util.record_time (fun uu____27940  -> nbe_eval c s t)
                  in
               match uu____27933 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27949  ->
                         let uu____27950 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27952 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27950 uu____27952);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____27960  ->
                   let uu____27961 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____27961);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____27967  ->
                   let uu____27968 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____27968);
              (let uu____27971 =
                 FStar_Util.record_time (fun uu____27978  -> norm c [] [] t)
                  in
               match uu____27971 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____27993  ->
                         let uu____27994 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____27996 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____27994 uu____27996);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____28015 =
          let uu____28019 =
            let uu____28021 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____28021  in
          FStar_Pervasives_Native.Some uu____28019  in
        FStar_Profiling.profile
          (fun uu____28024  -> normalize_with_primitive_steps [] s e t)
          uu____28015 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____28046  ->
             let uu____28047 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____28047);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____28053  ->
             let uu____28054 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____28054);
        (let uu____28057 =
           FStar_Util.record_time (fun uu____28064  -> norm_comp cfg [] c)
            in
         match uu____28057 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____28079  ->
                   let uu____28080 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____28082 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____28080
                     uu____28082);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____28096 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____28096 [] u
  
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
      let uu____28118 = normalize steps env t  in
      FStar_TypeChecker_Env.non_informative env uu____28118
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____28130 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env t ->
          let uu___3376_28149 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3376_28149.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3376_28149.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____28156 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____28156
          then
            let ct1 =
              let uu____28160 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____28160 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____28167 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____28167
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3386_28174 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3386_28174.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3386_28174.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3386_28174.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c
                     in
                  let uu___3390_28176 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3390_28176.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3390_28176.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3390_28176.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3390_28176.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3393_28177 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3393_28177.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3393_28177.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____28180 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      let uu____28192 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____28192
      then
        let uu____28195 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____28195 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3401_28199 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3401_28199.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3401_28199.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3401_28199.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3408_28218  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3407_28221 ->
            ((let uu____28223 =
                let uu____28229 =
                  let uu____28231 = FStar_Util.message_of_exn uu___3407_28221
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____28231
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____28229)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____28223);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3418_28250  ->
             match () with
             | () ->
                 let uu____28251 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____28251 [] c) ()
        with
        | uu___3417_28260 ->
            ((let uu____28262 =
                let uu____28268 =
                  let uu____28270 = FStar_Util.message_of_exn uu___3417_28260
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____28270
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____28268)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____28262);
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
                   let uu____28319 =
                     let uu____28320 =
                       let uu____28327 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____28327)  in
                     FStar_Syntax_Syntax.Tm_refine uu____28320  in
                   mk uu____28319 t01.FStar_Syntax_Syntax.pos
               | uu____28332 -> t2)
          | uu____28333 -> t2  in
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
        let uu____28427 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____28427 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____28464 ->
                 let uu____28473 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____28473 with
                  | (actuals,uu____28483,uu____28484) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____28504 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____28504 with
                         | (binders,args) ->
                             let uu____28515 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____28515
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
      | uu____28530 ->
          let uu____28531 = FStar_Syntax_Util.head_and_args t  in
          (match uu____28531 with
           | (head1,args) ->
               let uu____28574 =
                 let uu____28575 = FStar_Syntax_Subst.compress head1  in
                 uu____28575.FStar_Syntax_Syntax.n  in
               (match uu____28574 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____28596 =
                      let uu____28611 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____28611  in
                    (match uu____28596 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____28651 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3488_28659 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3488_28659.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3488_28659.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3488_28659.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3488_28659.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3488_28659.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3488_28659.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3488_28659.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3488_28659.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3488_28659.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3488_28659.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3488_28659.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3488_28659.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3488_28659.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3488_28659.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3488_28659.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3488_28659.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3488_28659.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3488_28659.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3488_28659.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3488_28659.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3488_28659.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3488_28659.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3488_28659.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3488_28659.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3488_28659.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3488_28659.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3488_28659.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3488_28659.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3488_28659.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3488_28659.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3488_28659.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3488_28659.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3488_28659.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3488_28659.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3488_28659.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3488_28659.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3488_28659.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3488_28659.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3488_28659.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3488_28659.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3488_28659.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3488_28659.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3488_28659.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____28651 with
                            | (uu____28662,ty,uu____28664) ->
                                eta_expand_with_type env t ty))
                | uu____28665 ->
                    let uu____28666 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3495_28674 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3495_28674.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3495_28674.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3495_28674.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3495_28674.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3495_28674.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3495_28674.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3495_28674.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3495_28674.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3495_28674.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3495_28674.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3495_28674.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3495_28674.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3495_28674.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3495_28674.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3495_28674.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3495_28674.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3495_28674.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3495_28674.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3495_28674.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3495_28674.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3495_28674.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3495_28674.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3495_28674.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3495_28674.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3495_28674.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3495_28674.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3495_28674.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3495_28674.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3495_28674.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3495_28674.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3495_28674.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3495_28674.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3495_28674.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3495_28674.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3495_28674.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3495_28674.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3495_28674.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3495_28674.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3495_28674.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3495_28674.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3495_28674.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3495_28674.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3495_28674.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____28666 with
                     | (uu____28677,ty,uu____28679) ->
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
      let uu___3507_28761 = x  in
      let uu____28762 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3507_28761.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3507_28761.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28762
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28765 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28789 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28790 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28791 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28792 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28799 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28800 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28801 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3533_28835 = rc  in
          let uu____28836 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28845 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3533_28835.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28836;
            FStar_Syntax_Syntax.residual_flags = uu____28845
          }  in
        let uu____28848 =
          let uu____28849 =
            let uu____28868 = elim_delayed_subst_binders bs  in
            let uu____28877 = elim_delayed_subst_term t2  in
            let uu____28880 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28868, uu____28877, uu____28880)  in
          FStar_Syntax_Syntax.Tm_abs uu____28849  in
        mk1 uu____28848
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____28917 =
          let uu____28918 =
            let uu____28933 = elim_delayed_subst_binders bs  in
            let uu____28942 = elim_delayed_subst_comp c  in
            (uu____28933, uu____28942)  in
          FStar_Syntax_Syntax.Tm_arrow uu____28918  in
        mk1 uu____28917
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____28961 =
          let uu____28962 =
            let uu____28969 = elim_bv bv  in
            let uu____28970 = elim_delayed_subst_term phi  in
            (uu____28969, uu____28970)  in
          FStar_Syntax_Syntax.Tm_refine uu____28962  in
        mk1 uu____28961
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____29001 =
          let uu____29002 =
            let uu____29019 = elim_delayed_subst_term t2  in
            let uu____29022 = elim_delayed_subst_args args  in
            (uu____29019, uu____29022)  in
          FStar_Syntax_Syntax.Tm_app uu____29002  in
        mk1 uu____29001
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3555_29094 = p  in
              let uu____29095 =
                let uu____29096 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____29096  in
              {
                FStar_Syntax_Syntax.v = uu____29095;
                FStar_Syntax_Syntax.p =
                  (uu___3555_29094.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3559_29098 = p  in
              let uu____29099 =
                let uu____29100 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____29100  in
              {
                FStar_Syntax_Syntax.v = uu____29099;
                FStar_Syntax_Syntax.p =
                  (uu___3559_29098.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3565_29107 = p  in
              let uu____29108 =
                let uu____29109 =
                  let uu____29116 = elim_bv x  in
                  let uu____29117 = elim_delayed_subst_term t0  in
                  (uu____29116, uu____29117)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____29109  in
              {
                FStar_Syntax_Syntax.v = uu____29108;
                FStar_Syntax_Syntax.p =
                  (uu___3565_29107.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3571_29142 = p  in
              let uu____29143 =
                let uu____29144 =
                  let uu____29158 =
                    FStar_List.map
                      (fun uu____29184  ->
                         match uu____29184 with
                         | (x,b) ->
                             let uu____29201 = elim_pat x  in
                             (uu____29201, b)) pats
                     in
                  (fv, uu____29158)  in
                FStar_Syntax_Syntax.Pat_cons uu____29144  in
              {
                FStar_Syntax_Syntax.v = uu____29143;
                FStar_Syntax_Syntax.p =
                  (uu___3571_29142.FStar_Syntax_Syntax.p)
              }
          | uu____29216 -> p  in
        let elim_branch uu____29240 =
          match uu____29240 with
          | (pat,wopt,t3) ->
              let uu____29266 = elim_pat pat  in
              let uu____29269 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____29272 = elim_delayed_subst_term t3  in
              (uu____29266, uu____29269, uu____29272)
           in
        let uu____29277 =
          let uu____29278 =
            let uu____29301 = elim_delayed_subst_term t2  in
            let uu____29304 = FStar_List.map elim_branch branches  in
            (uu____29301, uu____29304)  in
          FStar_Syntax_Syntax.Tm_match uu____29278  in
        mk1 uu____29277
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____29435 =
          match uu____29435 with
          | (tc,topt) ->
              let uu____29470 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____29480 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____29480
                | FStar_Util.Inr c ->
                    let uu____29482 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____29482
                 in
              let uu____29483 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____29470, uu____29483)
           in
        let uu____29492 =
          let uu____29493 =
            let uu____29520 = elim_delayed_subst_term t2  in
            let uu____29523 = elim_ascription a  in
            (uu____29520, uu____29523, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____29493  in
        mk1 uu____29492
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3601_29586 = lb  in
          let uu____29587 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____29590 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3601_29586.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3601_29586.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____29587;
            FStar_Syntax_Syntax.lbeff =
              (uu___3601_29586.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____29590;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3601_29586.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3601_29586.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____29593 =
          let uu____29594 =
            let uu____29608 =
              let uu____29616 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____29616)  in
            let uu____29628 = elim_delayed_subst_term t2  in
            (uu____29608, uu____29628)  in
          FStar_Syntax_Syntax.Tm_let uu____29594  in
        mk1 uu____29593
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____29673 =
          let uu____29674 =
            let uu____29681 = elim_delayed_subst_term tm  in
            (uu____29681, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____29674  in
        mk1 uu____29673
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29692 =
          let uu____29693 =
            let uu____29700 = elim_delayed_subst_term t2  in
            let uu____29703 = elim_delayed_subst_meta md  in
            (uu____29700, uu____29703)  in
          FStar_Syntax_Syntax.Tm_meta uu____29693  in
        mk1 uu____29692

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29712  ->
         match uu___17_29712 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29716 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29716
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
        let uu____29739 =
          let uu____29740 =
            let uu____29749 = elim_delayed_subst_term t  in
            (uu____29749, uopt)  in
          FStar_Syntax_Syntax.Total uu____29740  in
        mk1 uu____29739
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29766 =
          let uu____29767 =
            let uu____29776 = elim_delayed_subst_term t  in
            (uu____29776, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29767  in
        mk1 uu____29766
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3634_29785 = ct  in
          let uu____29786 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29789 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29800 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3634_29785.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3634_29785.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29786;
            FStar_Syntax_Syntax.effect_args = uu____29789;
            FStar_Syntax_Syntax.flags = uu____29800
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29803  ->
    match uu___18_29803 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____29838 =
          let uu____29859 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____29868 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29859, uu____29868)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29838
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____29923 =
          let uu____29930 = elim_delayed_subst_term t  in (m, uu____29930)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____29923
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____29942 =
          let uu____29951 = elim_delayed_subst_term t  in
          (m1, m2, uu____29951)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____29942
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
      (fun uu____29984  ->
         match uu____29984 with
         | (t,q) ->
             let uu____30003 = elim_delayed_subst_term t  in (uu____30003, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____30031  ->
         match uu____30031 with
         | (x,q) ->
             let uu____30050 =
               let uu___3660_30051 = x  in
               let uu____30052 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3660_30051.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3660_30051.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____30052
               }  in
             (uu____30050, q)) bs

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
            | (uu____30160,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____30192,FStar_Util.Inl t) ->
                let uu____30214 =
                  let uu____30221 =
                    let uu____30222 =
                      let uu____30237 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____30237)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____30222  in
                  FStar_Syntax_Syntax.mk uu____30221  in
                uu____30214 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____30250 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____30250 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____30282 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____30355 ->
                    let uu____30356 =
                      let uu____30365 =
                        let uu____30366 = FStar_Syntax_Subst.compress t4  in
                        uu____30366.FStar_Syntax_Syntax.n  in
                      (uu____30365, tc)  in
                    (match uu____30356 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____30395) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____30442) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____30487,FStar_Util.Inl uu____30488) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____30519 -> failwith "Impossible")
                 in
              (match uu____30282 with
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
          let uu____30658 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____30658 with
          | (univ_names1,binders1,tc) ->
              let uu____30732 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30732)
  
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
          let uu____30786 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____30786 with
          | (univ_names1,binders1,tc) ->
              let uu____30860 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30860)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____30902 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____30902 with
           | (univ_names1,binders1,typ1) ->
               let uu___3743_30942 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3743_30942.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3743_30942.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3743_30942.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3743_30942.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3743_30942.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3749_30957 = s  in
          let uu____30958 =
            let uu____30959 =
              let uu____30968 = FStar_List.map (elim_uvars env) sigs  in
              (uu____30968, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____30959  in
          {
            FStar_Syntax_Syntax.sigel = uu____30958;
            FStar_Syntax_Syntax.sigrng =
              (uu___3749_30957.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3749_30957.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3749_30957.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3749_30957.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3749_30957.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____30987 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30987 with
           | (univ_names1,uu____31011,typ1) ->
               let uu___3763_31033 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3763_31033.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3763_31033.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3763_31033.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3763_31033.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3763_31033.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____31040 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____31040 with
           | (univ_names1,uu____31064,typ1) ->
               let uu___3774_31086 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3774_31086.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3774_31086.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3774_31086.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3774_31086.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3774_31086.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____31116 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____31116 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____31141 =
                            let uu____31142 =
                              let uu____31143 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____31143  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____31142
                             in
                          elim_delayed_subst_term uu____31141  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3790_31146 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3790_31146.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3790_31146.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3790_31146.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3790_31146.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3793_31147 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3793_31147.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3793_31147.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3793_31147.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3793_31147.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3793_31147.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3797_31154 = s  in
          let uu____31155 =
            let uu____31156 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____31156  in
          {
            FStar_Syntax_Syntax.sigel = uu____31155;
            FStar_Syntax_Syntax.sigrng =
              (uu___3797_31154.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3797_31154.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3797_31154.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3797_31154.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3797_31154.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____31160 = elim_uvars_aux_t env us [] t  in
          (match uu____31160 with
           | (us1,uu____31184,t1) ->
               let uu___3808_31206 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3808_31206.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3808_31206.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3808_31206.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3808_31206.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3808_31206.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____31208 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____31208 with
           | (univs1,binders,uu____31227) ->
               let uu____31248 =
                 let uu____31253 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____31253 with
                 | (univs_opening,univs2) ->
                     let uu____31276 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____31276)
                  in
               (match uu____31248 with
                | (univs_opening,univs_closing) ->
                    let uu____31279 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____31285 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____31286 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____31285, uu____31286)  in
                    (match uu____31279 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____31312 =
                           match uu____31312 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____31330 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____31330 with
                                | (us1,t1) ->
                                    let uu____31341 =
                                      let uu____31350 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____31355 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____31350, uu____31355)  in
                                    (match uu____31341 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____31378 =
                                           let uu____31387 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____31392 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____31387, uu____31392)  in
                                         (match uu____31378 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____31416 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____31416
                                                 in
                                              let uu____31417 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____31417 with
                                               | (uu____31444,uu____31445,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____31468 =
                                                       let uu____31469 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____31469
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____31468
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____31478 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____31478 with
                           | (uu____31497,uu____31498,t1) -> t1  in
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
                             | uu____31574 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____31601 =
                               let uu____31602 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____31602.FStar_Syntax_Syntax.n  in
                             match uu____31601 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____31661 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31695 =
                               let uu____31696 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31696.FStar_Syntax_Syntax.n  in
                             match uu____31695 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31719) ->
                                 let uu____31744 = destruct_action_body body
                                    in
                                 (match uu____31744 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31793 ->
                                 let uu____31794 = destruct_action_body t  in
                                 (match uu____31794 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31849 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31849 with
                           | (action_univs,t) ->
                               let uu____31858 = destruct_action_typ_templ t
                                  in
                               (match uu____31858 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3892_31905 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3892_31905.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3892_31905.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3895_31907 = ed  in
                           let uu____31908 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____31909 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____31910 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3895_31907.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3895_31907.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____31908;
                             FStar_Syntax_Syntax.combinators = uu____31909;
                             FStar_Syntax_Syntax.actions = uu____31910;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3895_31907.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3898_31913 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3898_31913.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3898_31913.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3898_31913.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3898_31913.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3898_31913.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_31934 =
            match uu___19_31934 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____31965 = elim_uvars_aux_t env us [] t  in
                (match uu____31965 with
                 | (us1,uu____31997,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3913_32028 = sub_eff  in
            let uu____32029 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____32032 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3913_32028.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3913_32028.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____32029;
              FStar_Syntax_Syntax.lift = uu____32032
            }  in
          let uu___3916_32035 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3916_32035.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3916_32035.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3916_32035.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3916_32035.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3916_32035.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____32045 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____32045 with
           | (univ_names1,binders1,comp1) ->
               let uu___3929_32085 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3929_32085.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3929_32085.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3929_32085.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3929_32085.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3929_32085.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____32088 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____32089 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n1,p,(us_t,t),(us_ty,ty))
          ->
          let uu____32119 = elim_uvars_aux_t env us_t [] t  in
          (match uu____32119 with
           | (us_t1,uu____32143,t1) ->
               let uu____32165 = elim_uvars_aux_t env us_ty [] ty  in
               (match uu____32165 with
                | (us_ty1,uu____32189,ty1) ->
                    let uu___3954_32211 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n1, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3954_32211.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3954_32211.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3954_32211.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3954_32211.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3954_32211.FStar_Syntax_Syntax.sigopts)
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
        let uu____32262 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____32262 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____32284 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____32284 with
             | (uu____32291,head_def) ->
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
      let uu____32297 = FStar_Syntax_Util.head_and_args t  in
      match uu____32297 with
      | (head1,args) ->
          let uu____32342 =
            let uu____32343 = FStar_Syntax_Subst.compress head1  in
            uu____32343.FStar_Syntax_Syntax.n  in
          (match uu____32342 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____32350;
                  FStar_Syntax_Syntax.vars = uu____32351;_},us)
               -> aux fv us args
           | uu____32357 -> FStar_Pervasives_Native.None)
  