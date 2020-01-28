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
               | FStar_Syntax_Syntax.Tm_delayed uu____9705 ->
                   let uu____9728 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9728
               | uu____9731 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9741  ->
               let uu____9742 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9744 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9746 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9748 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9756 =
                 let uu____9758 =
                   let uu____9761 = firstn (Prims.of_int (4)) stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9761
                    in
                 stack_to_string uu____9758  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9742 uu____9744 uu____9746 uu____9748 uu____9756);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9789  ->
               let uu____9790 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9790);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9796  ->
                     let uu____9797 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9797);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9800 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9804  ->
                     let uu____9805 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9805);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____9808 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9812  ->
                     let uu____9813 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9813);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9816 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9820  ->
                     let uu____9821 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9821);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9824;
                 FStar_Syntax_Syntax.fv_delta = uu____9825;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9829  ->
                     let uu____9830 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9830);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9833;
                 FStar_Syntax_Syntax.fv_delta = uu____9834;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9835);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9845  ->
                     let uu____9846 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9846);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____9852 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____9852 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _9855) when
                    _9855 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9859  ->
                          let uu____9860 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9860);
                     rebuild cfg env stack t1)
                | uu____9863 ->
                    let uu____9866 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____9866 with
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
               let uu____9905 = closure_as_term cfg env t2  in
               rebuild cfg env stack uu____9905
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9933 = is_norm_request hd1 args  in
                  uu____9933 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____9939 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____9939))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9967 = is_norm_request hd1 args  in
                  uu____9967 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1261_9974 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1263_9977 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1263_9977.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1261_9974.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1261_9974.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1261_9974.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1261_9974.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1261_9974.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1261_9974.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____9984 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____9984 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____10020  ->
                                 fun stack1  ->
                                   match uu____10020 with
                                   | (a,aq) ->
                                       let uu____10032 =
                                         let uu____10033 =
                                           let uu____10040 =
                                             let uu____10041 =
                                               let uu____10073 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____10073, false)
                                                in
                                             Clos uu____10041  in
                                           (uu____10040, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10033  in
                                       uu____10032 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10141  ->
                            let uu____10142 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10142);
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
                         let uu____10174 =
                           let uu____10176 =
                             let uu____10178 = FStar_Util.time_diff start fin
                                in
                             FStar_Pervasives_Native.snd uu____10178  in
                           FStar_Util.string_of_int uu____10176  in
                         let uu____10185 =
                           FStar_Syntax_Print.term_to_string tm'  in
                         let uu____10187 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                         let uu____10189 =
                           FStar_Syntax_Print.term_to_string tm_norm  in
                         FStar_Util.print4
                           "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____10174 uu____10185 uu____10187 uu____10189)
                      else ();
                      rebuild cfg env stack tm_norm)
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     let delta_level =
                       let uu____10209 =
                         FStar_All.pipe_right s
                           (FStar_Util.for_some
                              (fun uu___13_10216  ->
                                 match uu___13_10216 with
                                 | FStar_TypeChecker_Env.UnfoldUntil
                                     uu____10218 -> true
                                 | FStar_TypeChecker_Env.UnfoldOnly
                                     uu____10220 -> true
                                 | FStar_TypeChecker_Env.UnfoldFully
                                     uu____10224 -> true
                                 | uu____10228 -> false))
                          in
                       if uu____10209
                       then
                         [FStar_TypeChecker_Env.Unfold
                            FStar_Syntax_Syntax.delta_constant]
                       else [FStar_TypeChecker_Env.NoDelta]  in
                     let cfg'1 =
                       let uu___1301_10236 = cfg  in
                       let uu____10237 =
                         let uu___1303_10238 =
                           FStar_TypeChecker_Cfg.to_fsteps s  in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                           FStar_TypeChecker_Cfg.unfold_until =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.unfold_until);
                           FStar_TypeChecker_Cfg.unfold_only =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.unfold_only);
                           FStar_TypeChecker_Cfg.unfold_fully =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.unfold_fully);
                           FStar_TypeChecker_Cfg.unfold_attr =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.unfold_attr);
                           FStar_TypeChecker_Cfg.unfold_tac =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request = true;
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1303_10238.FStar_TypeChecker_Cfg.for_extraction)
                         }  in
                       {
                         FStar_TypeChecker_Cfg.steps = uu____10237;
                         FStar_TypeChecker_Cfg.tcenv =
                           (uu___1301_10236.FStar_TypeChecker_Cfg.tcenv);
                         FStar_TypeChecker_Cfg.debug =
                           (uu___1301_10236.FStar_TypeChecker_Cfg.debug);
                         FStar_TypeChecker_Cfg.delta_level = delta_level;
                         FStar_TypeChecker_Cfg.primitive_steps =
                           (uu___1301_10236.FStar_TypeChecker_Cfg.primitive_steps);
                         FStar_TypeChecker_Cfg.strong =
                           (uu___1301_10236.FStar_TypeChecker_Cfg.strong);
                         FStar_TypeChecker_Cfg.memoize_lazy =
                           (uu___1301_10236.FStar_TypeChecker_Cfg.memoize_lazy);
                         FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                         FStar_TypeChecker_Cfg.reifying =
                           (uu___1301_10236.FStar_TypeChecker_Cfg.reifying)
                       }  in
                     let stack' =
                       let tail1 = (Cfg cfg) :: stack  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         let uu____10246 =
                           let uu____10247 =
                             let uu____10252 = FStar_Util.now ()  in
                             (tm, uu____10252)  in
                           Debug uu____10247  in
                         uu____10246 :: tail1
                       else tail1  in
                     norm cfg'1 env stack' tm))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10257 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10257
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10268 =
                      let uu____10275 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10275, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10268  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10284 = lookup_bvar env x  in
               (match uu____10284 with
                | Univ uu____10285 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____10339 = FStar_ST.op_Bang r  in
                      (match uu____10339 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10435  ->
                                 let uu____10436 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10438 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10436
                                   uu____10438);
                            (let uu____10441 = maybe_weakly_reduced t'  in
                             if uu____10441
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____10444 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10488)::uu____10489 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10500,uu____10501))::stack_rest ->
                    (match c with
                     | Univ uu____10505 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10514 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10544  ->
                                    let uu____10545 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10545);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10581  ->
                                    let uu____10582 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10582);
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
                       (fun uu____10630  ->
                          let uu____10631 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10631);
                     norm cfg env stack1 t1)
                | (Match uu____10634)::uu____10635 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10650 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10650 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10686  -> dummy :: env1) env)
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
                                          let uu____10730 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10730)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1421_10738 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1421_10738.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1421_10738.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10739 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10745  ->
                                 let uu____10746 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10746);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1428_10761 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1428_10761.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1428_10761.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1428_10761.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1428_10761.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1428_10761.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1428_10761.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1428_10761.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1428_10761.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____10765)::uu____10766 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10777 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10777 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10813  -> dummy :: env1) env)
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
                                          let uu____10857 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10857)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1421_10865 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1421_10865.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1421_10865.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10866 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10872  ->
                                 let uu____10873 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10873);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1428_10888 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1428_10888.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1428_10888.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1428_10888.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1428_10888.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1428_10888.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1428_10888.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1428_10888.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1428_10888.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10892)::uu____10893 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10906 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10906 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10942  -> dummy :: env1) env)
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
                                          let uu____10986 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10986)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1421_10994 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1421_10994.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1421_10994.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10995 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11001  ->
                                 let uu____11002 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11002);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1428_11017 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1428_11017.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1428_11017.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1428_11017.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1428_11017.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1428_11017.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1428_11017.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1428_11017.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1428_11017.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11021)::uu____11022 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11037 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11037 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11073  -> dummy :: env1) env)
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
                                          let uu____11117 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11117)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1421_11125 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1421_11125.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1421_11125.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11126 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11132  ->
                                 let uu____11133 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11133);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1428_11148 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1428_11148.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1428_11148.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1428_11148.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1428_11148.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1428_11148.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1428_11148.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1428_11148.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1428_11148.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11152)::uu____11153 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11168 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11168 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11204  -> dummy :: env1) env)
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
                                          let uu____11248 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11248)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1421_11256 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1421_11256.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1421_11256.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11257 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11263  ->
                                 let uu____11264 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11264);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1428_11279 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1428_11279.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1428_11279.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1428_11279.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1428_11279.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1428_11279.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1428_11279.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1428_11279.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1428_11279.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11283)::uu____11284 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11303 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11303 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11339  -> dummy :: env1) env)
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
                                          let uu____11383 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11383)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1421_11391 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1421_11391.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1421_11391.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11392 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11398  ->
                                 let uu____11399 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11399);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1428_11414 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1428_11414.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1428_11414.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1428_11414.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1428_11414.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1428_11414.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1428_11414.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1428_11414.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1428_11414.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____11422 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11422 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11458  -> dummy :: env1) env)
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
                                          let uu____11502 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11502)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1421_11510 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1421_11510.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1421_11510.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11511 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11517  ->
                                 let uu____11518 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11518);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1428_11533 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1428_11533.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1428_11533.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1428_11533.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1428_11533.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1428_11533.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1428_11533.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1428_11533.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1428_11533.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let strict_args =
                 let uu____11569 =
                   let uu____11570 = FStar_Syntax_Util.un_uinst head1  in
                   uu____11570.FStar_Syntax_Syntax.n  in
                 match uu____11569 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11579 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11600  ->
                              fun stack1  ->
                                match uu____11600 with
                                | (a,aq) ->
                                    let uu____11612 =
                                      let uu____11613 =
                                        let uu____11620 =
                                          let uu____11621 =
                                            let uu____11653 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11653, false)  in
                                          Clos uu____11621  in
                                        (uu____11620, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11613  in
                                    uu____11612 :: stack1) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11721  ->
                          let uu____11722 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11722);
                     norm cfg env stack1 head1)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____11773  ->
                              match uu____11773 with
                              | (a,i) ->
                                  let uu____11784 = norm cfg env [] a  in
                                  (uu____11784, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____11790 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____11805 = FStar_List.nth norm_args i
                                    in
                                 match uu____11805 with
                                 | (arg_i,uu____11816) ->
                                     let uu____11817 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____11817 with
                                      | (head2,uu____11836) ->
                                          let uu____11861 =
                                            let uu____11862 =
                                              FStar_Syntax_Util.un_uinst
                                                head2
                                               in
                                            uu____11862.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____11861 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____11866 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____11869 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____11869
                                           | uu____11870 -> false)))))
                       in
                    if uu____11790
                    then
                      let stack1 =
                        FStar_All.pipe_right stack
                          (FStar_List.fold_right
                             (fun uu____11887  ->
                                fun stack1  ->
                                  match uu____11887 with
                                  | (a,aq) ->
                                      let uu____11899 =
                                        let uu____11900 =
                                          let uu____11907 =
                                            let uu____11908 =
                                              let uu____11940 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env, a, uu____11940, false)
                                               in
                                            Clos uu____11908  in
                                          (uu____11907, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____11900  in
                                      uu____11899 :: stack1) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12022  ->
                            let uu____12023 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12023);
                       norm cfg env stack1 head1)
                    else
                      (let head2 = closure_as_term cfg env head1  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                           FStar_Pervasives_Native.None
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env stack term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12043) when
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
                             ((let uu___1490_12088 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1490_12088.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1490_12088.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12089 ->
                      let uu____12104 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12104)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12108 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12108 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12139 =
                          let uu____12140 =
                            let uu____12147 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1499_12153 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1499_12153.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1499_12153.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12147)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12140  in
                        mk uu____12139 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12177 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12177
               else
                 (let uu____12180 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12180 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12188 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12214  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12188 c1  in
                      let t2 =
                        let uu____12238 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12238 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12351)::uu____12352 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12365  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12367)::uu____12368 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12379  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12381,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12382;
                                   FStar_Syntax_Syntax.vars = uu____12383;_},uu____12384,uu____12385))::uu____12386
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12393  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12395)::uu____12396 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12407  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12409 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12412  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12417  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12443 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12443
                         | FStar_Util.Inr c ->
                             let uu____12457 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12457
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12480 =
                               let uu____12481 =
                                 let uu____12508 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12508, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12481
                                in
                             mk uu____12480 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12543 ->
                           let uu____12544 =
                             let uu____12545 =
                               let uu____12546 =
                                 let uu____12573 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12573, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12546
                                in
                             mk uu____12545 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12544))))
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
                   let uu___1578_12651 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1580_12654 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1580_12654.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1578_12651.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1578_12651.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1578_12651.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1578_12651.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1578_12651.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1578_12651.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1578_12651.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1578_12651.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____12695 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12695 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1593_12715 = cfg  in
                               let uu____12716 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1593_12715.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12716;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1593_12715.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1593_12715.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1593_12715.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1593_12715.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1593_12715.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1593_12715.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1593_12715.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____12723 =
                                 let uu____12724 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12724  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12723
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1600_12727 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1600_12727.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1600_12727.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1600_12727.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1600_12727.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12728 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12728
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12741,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12742;
                               FStar_Syntax_Syntax.lbunivs = uu____12743;
                               FStar_Syntax_Syntax.lbtyp = uu____12744;
                               FStar_Syntax_Syntax.lbeff = uu____12745;
                               FStar_Syntax_Syntax.lbdef = uu____12746;
                               FStar_Syntax_Syntax.lbattrs = uu____12747;
                               FStar_Syntax_Syntax.lbpos = uu____12748;_}::uu____12749),uu____12750)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let uu____12795 =
                 FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
               if uu____12795
               then
                 let binder =
                   let uu____12799 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12799  in
                 let env1 =
                   let uu____12809 =
                     let uu____12816 =
                       let uu____12817 =
                         let uu____12849 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12849,
                           false)
                          in
                       Clos uu____12817  in
                     ((FStar_Pervasives_Native.Some binder), uu____12816)  in
                   uu____12809 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____12924  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____12931  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12933 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12933))
                 else
                   (let uu____12936 =
                      let uu____12941 =
                        let uu____12942 =
                          let uu____12949 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12949
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12942]  in
                      FStar_Syntax_Subst.open_term uu____12941 body  in
                    match uu____12936 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____12976  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12985 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12985  in
                            FStar_Util.Inl
                              (let uu___1641_13001 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1641_13001.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1641_13001.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____13004  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___1646_13007 = lb  in
                             let uu____13008 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu____13011 =
                               FStar_List.map (norm cfg env [])
                                 lb.FStar_Syntax_Syntax.lbattrs
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1646_13007.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1646_13007.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13008;
                               FStar_Syntax_Syntax.lbattrs = uu____13011;
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1646_13007.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13046  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___1653_13071 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___1653_13071.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___1653_13071.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___1653_13071.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___1653_13071.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___1653_13071.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___1653_13071.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___1653_13071.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___1653_13071.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____13075  ->
                                FStar_Util.print_string
                                  "+++ Normalizing Tm_let -- body\n");
                           norm cfg1 env'
                             ((Let
                                 (env, bs, lb1, (t1.FStar_Syntax_Syntax.pos)))
                             :: stack1) body1))))
           | FStar_Syntax_Syntax.Tm_let ((true ,lbs),body) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                 ||
                 ((Prims.op_Negation
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                    &&
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations)
               ->
               let uu____13096 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13096 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13132 =
                               let uu___1669_13133 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1669_13133.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1669_13133.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13132  in
                           let uu____13134 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13134 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13160 =
                                   FStar_List.map (fun uu____13182  -> dummy)
                                     xs1
                                    in
                                 let uu____13189 =
                                   let uu____13198 =
                                     FStar_List.map
                                       (fun uu____13214  -> dummy) lbs1
                                      in
                                   FStar_List.append uu____13198 env  in
                                 FStar_List.append uu____13160 uu____13189
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13234 =
                                       let uu___1683_13235 = rc  in
                                       let uu____13236 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1683_13235.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13236;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1683_13235.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13234
                                 | uu____13245 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1688_13251 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1688_13251.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1688_13251.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1688_13251.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1688_13251.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13261 =
                        FStar_List.map (fun uu____13277  -> dummy) lbs2  in
                      FStar_List.append uu____13261 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13285 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13285 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1697_13301 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1697_13301.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1697_13301.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____13335 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13335
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13356 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13434  ->
                        match uu____13434 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1713_13559 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1713_13559.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1713_13559.FStar_Syntax_Syntax.sort)
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
               (match uu____13356 with
                | (rec_env,memos,uu____13750) ->
                    let uu____13805 =
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
                             let uu____14054 =
                               let uu____14061 =
                                 let uu____14062 =
                                   let uu____14094 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14094, false)
                                    in
                                 Clos uu____14062  in
                               (FStar_Pervasives_Native.None, uu____14061)
                                in
                             uu____14054 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14179  ->
                     let uu____14180 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14180);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14204 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14208::uu____14209 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14214) ->
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
                             | uu____14293 -> norm cfg env stack head1)
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
                                  let uu____14341 =
                                    let uu____14362 =
                                      norm_pattern_args cfg env args  in
                                    (names2, uu____14362)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14341
                              | uu____14391 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14397 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14421 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14435 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14449 =
                        let uu____14451 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14453 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14451 uu____14453
                         in
                      failwith uu____14449
                    else
                      (let uu____14458 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____14458)
                | uu____14459 -> norm cfg env stack t2))

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
              let uu____14468 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14468 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14482  ->
                        let uu____14483 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14483);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14496  ->
                        let uu____14497 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14499 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14497 uu____14499);
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
                      | (UnivArgs (us',uu____14512))::stack1 ->
                          ((let uu____14521 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14521
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14529 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14529) us'
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
                      | uu____14565 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14568 ->
                          let uu____14571 =
                            let uu____14573 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14573
                             in
                          failwith uu____14571
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
                  let uu___1825_14601 = cfg  in
                  let uu____14602 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____14602;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1825_14601.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1825_14601.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1825_14601.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1825_14601.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1825_14601.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1825_14601.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1825_14601.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____14633,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14634;
                                    FStar_Syntax_Syntax.vars = uu____14635;_},uu____14636,uu____14637))::uu____14638
                     -> ()
                 | uu____14643 ->
                     let uu____14646 =
                       let uu____14648 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14648
                        in
                     failwith uu____14646);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____14657  ->
                      let uu____14658 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____14660 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____14658
                        uu____14660);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____14664 =
                    let uu____14665 = FStar_Syntax_Subst.compress head3  in
                    uu____14665.FStar_Syntax_Syntax.n  in
                  match uu____14664 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____14686 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____14686
                         in
                      let uu____14687 =
                        let uu____14696 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_bind_repr
                           in
                        FStar_All.pipe_right uu____14696 FStar_Util.must  in
                      (match uu____14687 with
                       | (uu____14711,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14721 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____14732 =
                                    let uu____14733 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14733.FStar_Syntax_Syntax.n  in
                                  match uu____14732 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____14739,uu____14740))
                                      ->
                                      let uu____14749 =
                                        let uu____14750 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____14750.FStar_Syntax_Syntax.n  in
                                      (match uu____14749 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____14756,msrc,uu____14758))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____14767 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____14767
                                       | uu____14768 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____14769 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____14770 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____14770 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___1897_14775 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___1897_14775.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___1897_14775.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___1897_14775.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___1897_14775.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___1897_14775.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____14776 = FStar_List.tl stack
                                        in
                                     let uu____14777 =
                                       let uu____14778 =
                                         let uu____14785 =
                                           let uu____14786 =
                                             let uu____14800 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____14800)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____14786
                                            in
                                         FStar_Syntax_Syntax.mk uu____14785
                                          in
                                       uu____14778
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____14776 uu____14777
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____14816 =
                                       let uu____14818 = is_return body  in
                                       match uu____14818 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____14823;
                                             FStar_Syntax_Syntax.vars =
                                               uu____14824;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____14827 -> false  in
                                     if uu____14816
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
                                          let uu____14851 =
                                            let uu____14858 =
                                              let uu____14859 =
                                                let uu____14878 =
                                                  let uu____14887 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____14887]  in
                                                (uu____14878, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____14859
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____14858
                                             in
                                          uu____14851
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____14926 =
                                            let uu____14927 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____14927.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14926 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____14933::uu____14934::[])
                                              ->
                                              let uu____14939 =
                                                let uu____14946 =
                                                  let uu____14947 =
                                                    let uu____14954 =
                                                      let uu____14955 =
                                                        let uu____14956 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____14956
                                                         in
                                                      let uu____14957 =
                                                        let uu____14960 =
                                                          let uu____14961 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____14961
                                                           in
                                                        [uu____14960]  in
                                                      uu____14955 ::
                                                        uu____14957
                                                       in
                                                    (bind1, uu____14954)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____14947
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____14946
                                                 in
                                              uu____14939
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____14964 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____14979 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____14979
                                          then
                                            let uu____14992 =
                                              let uu____15001 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____15001
                                               in
                                            let uu____15002 =
                                              let uu____15013 =
                                                let uu____15022 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____15022
                                                 in
                                              [uu____15013]  in
                                            uu____14992 :: uu____15002
                                          else []  in
                                        let reified =
                                          let args =
                                            let uu____15071 =
                                              FStar_Syntax_Util.is_layered ed
                                               in
                                            if uu____15071
                                            then
                                              let unit_args =
                                                let uu____15095 =
                                                  let uu____15096 =
                                                    let uu____15099 =
                                                      let uu____15100 =
                                                        FStar_All.pipe_right
                                                          ed
                                                          FStar_Syntax_Util.get_bind_vc_combinator
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____15100
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15099
                                                      FStar_Syntax_Subst.compress
                                                     in
                                                  uu____15096.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____15095 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (uu____15141::uu____15142::bs,uu____15144)
                                                    when
                                                    (FStar_List.length bs) >=
                                                      (Prims.of_int (2))
                                                    ->
                                                    let uu____15196 =
                                                      let uu____15205 =
                                                        FStar_All.pipe_right
                                                          bs
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs)
                                                                -
                                                                (Prims.of_int (2))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____15205
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15196
                                                      (FStar_List.map
                                                         (fun uu____15336  ->
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.unit_const))
                                                | uu____15343 ->
                                                    let uu____15344 =
                                                      let uu____15350 =
                                                        let uu____15352 =
                                                          FStar_Ident.string_of_lid
                                                            ed.FStar_Syntax_Syntax.mname
                                                           in
                                                        let uu____15354 =
                                                          let uu____15356 =
                                                            let uu____15357 =
                                                              FStar_All.pipe_right
                                                                ed
                                                                FStar_Syntax_Util.get_bind_vc_combinator
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____15357
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____15356
                                                            FStar_Syntax_Print.term_to_string
                                                           in
                                                        FStar_Util.format2
                                                          "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                          uu____15352
                                                          uu____15354
                                                         in
                                                      (FStar_Errors.Fatal_UnexpectedEffect,
                                                        uu____15350)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____15344 rng
                                                 in
                                              let uu____15391 =
                                                FStar_Syntax_Syntax.as_arg
                                                  lb.FStar_Syntax_Syntax.lbtyp
                                                 in
                                              let uu____15400 =
                                                let uu____15411 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____15420 =
                                                  let uu____15431 =
                                                    let uu____15442 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head4
                                                       in
                                                    let uu____15451 =
                                                      let uu____15462 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          body2
                                                         in
                                                      [uu____15462]  in
                                                    uu____15442 ::
                                                      uu____15451
                                                     in
                                                  FStar_List.append unit_args
                                                    uu____15431
                                                   in
                                                uu____15411 :: uu____15420
                                                 in
                                              uu____15391 :: uu____15400
                                            else
                                              (let uu____15521 =
                                                 let uu____15532 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____15541 =
                                                   let uu____15552 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   [uu____15552]  in
                                                 uu____15532 :: uu____15541
                                                  in
                                               let uu____15585 =
                                                 let uu____15596 =
                                                   let uu____15607 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       FStar_Syntax_Syntax.tun
                                                      in
                                                   let uu____15616 =
                                                     let uu____15627 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         head4
                                                        in
                                                     let uu____15636 =
                                                       let uu____15647 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let uu____15656 =
                                                         let uu____15667 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2
                                                            in
                                                         [uu____15667]  in
                                                       uu____15647 ::
                                                         uu____15656
                                                        in
                                                     uu____15627 ::
                                                       uu____15636
                                                      in
                                                   uu____15607 :: uu____15616
                                                    in
                                                 FStar_List.append
                                                   maybe_range_arg
                                                   uu____15596
                                                  in
                                               FStar_List.append uu____15521
                                                 uu____15585)
                                             in
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (bind_inst, args))
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____15748  ->
                                             let uu____15749 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____15751 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____15749 uu____15751);
                                        (let uu____15754 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____15754 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____15782 = FStar_Options.defensive ()  in
                        if uu____15782
                        then
                          let is_arg_impure uu____15797 =
                            match uu____15797 with
                            | (e,q) ->
                                let uu____15811 =
                                  let uu____15812 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____15812.FStar_Syntax_Syntax.n  in
                                (match uu____15811 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____15828 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____15828
                                 | uu____15830 -> false)
                             in
                          let uu____15832 =
                            let uu____15834 =
                              let uu____15845 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____15845 :: args  in
                            FStar_Util.for_some is_arg_impure uu____15834  in
                          (if uu____15832
                           then
                             let uu____15871 =
                               let uu____15877 =
                                 let uu____15879 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____15879
                                  in
                               (FStar_Errors.Warning_Defensive, uu____15877)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____15871
                           else ())
                        else ());
                       (let fallback1 uu____15892 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15896  ->
                               let uu____15897 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____15897 "");
                          (let uu____15901 = FStar_List.tl stack  in
                           let uu____15902 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____15901 uu____15902)
                           in
                        let fallback2 uu____15908 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15912  ->
                               let uu____15913 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____15913 "");
                          (let uu____15917 = FStar_List.tl stack  in
                           let uu____15918 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____15917 uu____15918)
                           in
                        let uu____15923 =
                          let uu____15924 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____15924.FStar_Syntax_Syntax.n  in
                        match uu____15923 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____15930 =
                              let uu____15932 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____15932  in
                            if uu____15930
                            then fallback1 ()
                            else
                              (let uu____15937 =
                                 let uu____15939 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____15939  in
                               if uu____15937
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____15956 =
                                      let uu____15961 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____15961 args
                                       in
                                    uu____15956 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____15962 = FStar_List.tl stack  in
                                  norm cfg env uu____15962 t1))
                        | uu____15963 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____15965) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____15989 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____15989  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____15993  ->
                            let uu____15994 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____15994);
                       (let uu____15997 = FStar_List.tl stack  in
                        norm cfg env uu____15997 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____16118  ->
                                match uu____16118 with
                                | (pat,wopt,tm) ->
                                    let uu____16166 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16166)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____16198 = FStar_List.tl stack  in
                      norm cfg env uu____16198 tm
                  | uu____16199 -> fallback ()))

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
              (fun uu____16213  ->
                 let uu____16214 = FStar_Ident.string_of_lid msrc  in
                 let uu____16216 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16218 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16214
                   uu____16216 uu____16218);
            (let uu____16221 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16224 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env)
                     in
                  Prims.op_Negation uu____16224)
                in
             if uu____16221
             then
               let ed =
                 let uu____16229 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16229  in
               let uu____16230 =
                 let uu____16237 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr
                    in
                 FStar_All.pipe_right uu____16237 FStar_Util.must  in
               match uu____16230 with
               | (uu____16274,return_repr) ->
                   let return_inst =
                     let uu____16283 =
                       let uu____16284 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____16284.FStar_Syntax_Syntax.n  in
                     match uu____16283 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16290::[]) ->
                         let uu____16295 =
                           let uu____16302 =
                             let uu____16303 =
                               let uu____16310 =
                                 let uu____16311 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____16311]  in
                               (return_tm, uu____16310)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____16303  in
                           FStar_Syntax_Syntax.mk uu____16302  in
                         uu____16295 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16314 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____16318 =
                     let uu____16325 =
                       let uu____16326 =
                         let uu____16343 =
                           let uu____16354 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____16363 =
                             let uu____16374 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____16374]  in
                           uu____16354 :: uu____16363  in
                         (return_inst, uu____16343)  in
                       FStar_Syntax_Syntax.Tm_app uu____16326  in
                     FStar_Syntax_Syntax.mk uu____16325  in
                   uu____16318 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____16421 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____16421 with
                | FStar_Pervasives_Native.None  ->
                    let uu____16424 =
                      let uu____16426 = FStar_Ident.text_of_lid msrc  in
                      let uu____16428 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____16426 uu____16428
                       in
                    failwith uu____16424
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16431;
                      FStar_TypeChecker_Env.mtarget = uu____16432;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16433;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____16453 =
                      let uu____16455 = FStar_Ident.text_of_lid msrc  in
                      let uu____16457 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____16455 uu____16457
                       in
                    failwith uu____16453
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16460;
                      FStar_TypeChecker_Env.mtarget = uu____16461;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16462;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____16493 =
                        FStar_TypeChecker_Env.is_reifiable_effect env msrc
                         in
                      if uu____16493
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____16498 =
                           let uu____16505 =
                             let uu____16506 =
                               let uu____16525 =
                                 let uu____16534 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____16534]  in
                               (uu____16525, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____16506  in
                           FStar_Syntax_Syntax.mk uu____16505  in
                         uu____16498 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____16567 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    lift uu____16567 t e1))

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
                (fun uu____16637  ->
                   match uu____16637 with
                   | (a,imp) ->
                       let uu____16656 = norm cfg env [] a  in
                       (uu____16656, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____16666  ->
             let uu____16667 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____16669 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____16667 uu____16669);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16695 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16698  -> FStar_Pervasives_Native.Some _16698)
                     uu____16695
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2062_16699 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2062_16699.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2062_16699.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16721 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16724  -> FStar_Pervasives_Native.Some _16724)
                     uu____16721
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2073_16725 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2073_16725.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2073_16725.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____16770  ->
                      match uu____16770 with
                      | (a,i) ->
                          let uu____16790 = norm cfg env [] a  in
                          (uu____16790, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_16812  ->
                       match uu___14_16812 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____16816 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____16816
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2090_16824 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2092_16827 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2092_16827.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2090_16824.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2090_16824.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____16831 = b  in
        match uu____16831 with
        | (x,imp) ->
            let x1 =
              let uu___2100_16839 = x  in
              let uu____16840 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2100_16839.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2100_16839.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16840
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____16851 =
                    let uu____16852 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____16852  in
                  FStar_Pervasives_Native.Some uu____16851
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16863 =
          FStar_List.fold_left
            (fun uu____16897  ->
               fun b  ->
                 match uu____16897 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16863 with | (nbs,uu____16977) -> FStar_List.rev nbs

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
            let uu____17009 =
              let uu___2125_17010 = rc  in
              let uu____17011 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2125_17010.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17011;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2125_17010.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17009
        | uu____17029 -> lopt

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
            (let uu____17039 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17041 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17039 uu____17041)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_17053  ->
      match uu___15_17053 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17066 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17066 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17070 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____17070)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____17078 = norm_cb cfg  in
            reduce_primops uu____17078 cfg env tm  in
          let uu____17083 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17083
          then tm1
          else
            (let w t =
               let uu___2154_17102 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2154_17102.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2154_17102.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17114 =
                 let uu____17115 = FStar_Syntax_Util.unmeta t  in
                 uu____17115.FStar_Syntax_Syntax.n  in
               match uu____17114 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17127 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17191)::args1,(bv,uu____17194)::bs1) ->
                   let uu____17248 =
                     let uu____17249 = FStar_Syntax_Subst.compress t  in
                     uu____17249.FStar_Syntax_Syntax.n  in
                   (match uu____17248 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17254 -> false)
               | ([],[]) -> true
               | (uu____17285,uu____17286) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17337 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17339 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17337
                    uu____17339)
               else ();
               (let uu____17344 = FStar_Syntax_Util.head_and_args' t  in
                match uu____17344 with
                | (hd1,args) ->
                    let uu____17383 =
                      let uu____17384 = FStar_Syntax_Subst.compress hd1  in
                      uu____17384.FStar_Syntax_Syntax.n  in
                    (match uu____17383 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____17392 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____17394 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____17396 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17392 uu____17394 uu____17396)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17401 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17419 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17421 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17419
                    uu____17421)
               else ();
               (let uu____17426 = FStar_Syntax_Util.is_squash t  in
                match uu____17426 with
                | FStar_Pervasives_Native.Some (uu____17437,t') ->
                    is_applied bs t'
                | uu____17449 ->
                    let uu____17458 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____17458 with
                     | FStar_Pervasives_Native.Some (uu____17469,t') ->
                         is_applied bs t'
                     | uu____17481 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____17505 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17505 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17512)::(q,uu____17514)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17557 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____17559 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17557 uu____17559)
                    else ();
                    (let uu____17564 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____17564 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17569 =
                           let uu____17570 = FStar_Syntax_Subst.compress p
                              in
                           uu____17570.FStar_Syntax_Syntax.n  in
                         (match uu____17569 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____17581 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17581))
                          | uu____17584 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____17587)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____17612 =
                           let uu____17613 = FStar_Syntax_Subst.compress p1
                              in
                           uu____17613.FStar_Syntax_Syntax.n  in
                         (match uu____17612 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____17624 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17624))
                          | uu____17627 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____17631 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____17631 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____17636 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____17636 with
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
                                     let uu____17650 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17650))
                               | uu____17653 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____17658)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____17683 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____17683 with
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
                                     let uu____17697 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17697))
                               | uu____17700 -> FStar_Pervasives_Native.None)
                          | uu____17703 -> FStar_Pervasives_Native.None)
                     | uu____17706 -> FStar_Pervasives_Native.None))
               | uu____17709 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____17722 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17722 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____17728)::[],uu____17729,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17749 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____17751 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____17749
                         uu____17751)
                    else ();
                    is_quantified_const bv phi')
               | uu____17756 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____17771 =
                 let uu____17772 = FStar_Syntax_Subst.compress phi  in
                 uu____17772.FStar_Syntax_Syntax.n  in
               match uu____17771 with
               | FStar_Syntax_Syntax.Tm_match (uu____17778,br::brs) ->
                   let uu____17845 = br  in
                   (match uu____17845 with
                    | (uu____17863,uu____17864,e) ->
                        let r =
                          let uu____17886 = simp_t e  in
                          match uu____17886 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____17898 =
                                FStar_List.for_all
                                  (fun uu____17917  ->
                                     match uu____17917 with
                                     | (uu____17931,uu____17932,e') ->
                                         let uu____17946 = simp_t e'  in
                                         uu____17946 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____17898
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____17962 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____17972 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____17972
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18010 =
                 match uu____18010 with
                 | (t1,q) ->
                     let uu____18031 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18031 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18063 -> (t1, q))
                  in
               let uu____18076 = FStar_Syntax_Util.head_and_args t  in
               match uu____18076 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18156 =
                 let uu____18157 = FStar_Syntax_Util.unmeta ty  in
                 uu____18157.FStar_Syntax_Syntax.n  in
               match uu____18156 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18162) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18167,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18191 -> false  in
             let simplify1 arg =
               let uu____18224 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18224, arg)  in
             let uu____18239 = is_forall_const tm1  in
             match uu____18239 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____18245 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18247 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18245
                       uu____18247)
                  else ();
                  (let uu____18252 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18252))
             | FStar_Pervasives_Native.None  ->
                 let uu____18253 =
                   let uu____18254 = FStar_Syntax_Subst.compress tm1  in
                   uu____18254.FStar_Syntax_Syntax.n  in
                 (match uu____18253 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18258;
                              FStar_Syntax_Syntax.vars = uu____18259;_},uu____18260);
                         FStar_Syntax_Syntax.pos = uu____18261;
                         FStar_Syntax_Syntax.vars = uu____18262;_},args)
                      ->
                      let uu____18292 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18292
                      then
                        let uu____18295 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18295 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18353)::
                             (uu____18354,(arg,uu____18356))::[] ->
                             maybe_auto_squash arg
                         | (uu____18429,(arg,uu____18431))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18432)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18505)::uu____18506::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18576::(FStar_Pervasives_Native.Some (false
                                         ),uu____18577)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18647 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18665 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18665
                         then
                           let uu____18668 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18668 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18726)::uu____18727::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18797::(FStar_Pervasives_Native.Some (true
                                           ),uu____18798)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18868)::(uu____18869,(arg,uu____18871))::[]
                               -> maybe_auto_squash arg
                           | (uu____18944,(arg,uu____18946))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18947)::[]
                               -> maybe_auto_squash arg
                           | uu____19020 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19038 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19038
                            then
                              let uu____19041 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19041 with
                              | uu____19099::(FStar_Pervasives_Native.Some
                                              (true ),uu____19100)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19170)::uu____19171::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19241)::(uu____19242,(arg,uu____19244))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19317,(p,uu____19319))::(uu____19320,
                                                                (q,uu____19322))::[]
                                  ->
                                  let uu____19394 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19394
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19399 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19417 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19417
                               then
                                 let uu____19420 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19420 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19478)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19479)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19553)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19554)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19628)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19629)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19703)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19704)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19778,(arg,uu____19780))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19781)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19854)::(uu____19855,(arg,uu____19857))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19930,(arg,uu____19932))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19933)::[]
                                     ->
                                     let uu____20006 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20006
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20007)::(uu____20008,(arg,uu____20010))::[]
                                     ->
                                     let uu____20083 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20083
                                 | (uu____20084,(p,uu____20086))::(uu____20087,
                                                                   (q,uu____20089))::[]
                                     ->
                                     let uu____20161 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20161
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20166 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20184 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20184
                                  then
                                    let uu____20187 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20187 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20245)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20289)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20333 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20351 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20351
                                     then
                                       match args with
                                       | (t,uu____20355)::[] ->
                                           let uu____20380 =
                                             let uu____20381 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20381.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20380 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20384::[],body,uu____20386)
                                                ->
                                                let uu____20421 = simp_t body
                                                   in
                                                (match uu____20421 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20427 -> tm1)
                                            | uu____20431 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20433))::(t,uu____20435)::[]
                                           ->
                                           let uu____20475 =
                                             let uu____20476 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20476.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20475 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20479::[],body,uu____20481)
                                                ->
                                                let uu____20516 = simp_t body
                                                   in
                                                (match uu____20516 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20524 -> tm1)
                                            | uu____20528 -> tm1)
                                       | uu____20529 -> tm1
                                     else
                                       (let uu____20542 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20542
                                        then
                                          match args with
                                          | (t,uu____20546)::[] ->
                                              let uu____20571 =
                                                let uu____20572 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20572.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20571 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20575::[],body,uu____20577)
                                                   ->
                                                   let uu____20612 =
                                                     simp_t body  in
                                                   (match uu____20612 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20618 -> tm1)
                                               | uu____20622 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20624))::(t,uu____20626)::[]
                                              ->
                                              let uu____20666 =
                                                let uu____20667 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20667.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20666 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20670::[],body,uu____20672)
                                                   ->
                                                   let uu____20707 =
                                                     simp_t body  in
                                                   (match uu____20707 with
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
                                                    | uu____20715 -> tm1)
                                               | uu____20719 -> tm1)
                                          | uu____20720 -> tm1
                                        else
                                          (let uu____20733 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20733
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20736;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20737;_},uu____20738)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20764;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20765;_},uu____20766)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20792 -> tm1
                                           else
                                             (let uu____20805 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____20805
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____20819 =
                                                    let uu____20820 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____20820.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____20819 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____20831 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____20845 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____20845
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____20884 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____20884
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____20890 =
                                                         let uu____20891 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____20891.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____20890 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____20894 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____20902 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____20902
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____20911
                                                                  =
                                                                  let uu____20912
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____20912.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____20911
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____20918)
                                                                    -> hd1
                                                                | uu____20943
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____20947
                                                                =
                                                                let uu____20958
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____20958]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____20947)
                                                       | uu____20991 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____20996 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____20996 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21016 ->
                                                     let uu____21025 =
                                                       let uu____21032 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____21032 cfg env
                                                        in
                                                     uu____21025 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21038;
                         FStar_Syntax_Syntax.vars = uu____21039;_},args)
                      ->
                      let uu____21065 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21065
                      then
                        let uu____21068 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21068 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21126)::
                             (uu____21127,(arg,uu____21129))::[] ->
                             maybe_auto_squash arg
                         | (uu____21202,(arg,uu____21204))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21205)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21278)::uu____21279::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21349::(FStar_Pervasives_Native.Some (false
                                         ),uu____21350)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21420 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21438 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21438
                         then
                           let uu____21441 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21441 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21499)::uu____21500::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21570::(FStar_Pervasives_Native.Some (true
                                           ),uu____21571)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21641)::(uu____21642,(arg,uu____21644))::[]
                               -> maybe_auto_squash arg
                           | (uu____21717,(arg,uu____21719))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21720)::[]
                               -> maybe_auto_squash arg
                           | uu____21793 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21811 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21811
                            then
                              let uu____21814 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21814 with
                              | uu____21872::(FStar_Pervasives_Native.Some
                                              (true ),uu____21873)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21943)::uu____21944::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22014)::(uu____22015,(arg,uu____22017))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22090,(p,uu____22092))::(uu____22093,
                                                                (q,uu____22095))::[]
                                  ->
                                  let uu____22167 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22167
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22172 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22190 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22190
                               then
                                 let uu____22193 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____22193 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22251)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22252)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22326)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22327)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22401)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22402)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22476)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22477)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22551,(arg,uu____22553))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22554)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22627)::(uu____22628,(arg,uu____22630))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____22703,(arg,uu____22705))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____22706)::[]
                                     ->
                                     let uu____22779 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22779
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22780)::(uu____22781,(arg,uu____22783))::[]
                                     ->
                                     let uu____22856 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22856
                                 | (uu____22857,(p,uu____22859))::(uu____22860,
                                                                   (q,uu____22862))::[]
                                     ->
                                     let uu____22934 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22934
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22939 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22957 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22957
                                  then
                                    let uu____22960 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22960 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23018)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23062)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23106 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23124 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23124
                                     then
                                       match args with
                                       | (t,uu____23128)::[] ->
                                           let uu____23153 =
                                             let uu____23154 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23154.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23153 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23157::[],body,uu____23159)
                                                ->
                                                let uu____23194 = simp_t body
                                                   in
                                                (match uu____23194 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23200 -> tm1)
                                            | uu____23204 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23206))::(t,uu____23208)::[]
                                           ->
                                           let uu____23248 =
                                             let uu____23249 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23249.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23248 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23252::[],body,uu____23254)
                                                ->
                                                let uu____23289 = simp_t body
                                                   in
                                                (match uu____23289 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____23297 -> tm1)
                                            | uu____23301 -> tm1)
                                       | uu____23302 -> tm1
                                     else
                                       (let uu____23315 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____23315
                                        then
                                          match args with
                                          | (t,uu____23319)::[] ->
                                              let uu____23344 =
                                                let uu____23345 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23345.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23344 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23348::[],body,uu____23350)
                                                   ->
                                                   let uu____23385 =
                                                     simp_t body  in
                                                   (match uu____23385 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____23391 -> tm1)
                                               | uu____23395 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____23397))::(t,uu____23399)::[]
                                              ->
                                              let uu____23439 =
                                                let uu____23440 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23440.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23439 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23443::[],body,uu____23445)
                                                   ->
                                                   let uu____23480 =
                                                     simp_t body  in
                                                   (match uu____23480 with
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
                                                    | uu____23488 -> tm1)
                                               | uu____23492 -> tm1)
                                          | uu____23493 -> tm1
                                        else
                                          (let uu____23506 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____23506
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23509;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23510;_},uu____23511)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23537;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23538;_},uu____23539)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____23565 -> tm1
                                           else
                                             (let uu____23578 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____23578
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____23592 =
                                                    let uu____23593 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____23593.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____23592 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____23604 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____23618 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____23618
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____23653 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____23653
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____23659 =
                                                         let uu____23660 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____23660.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____23659 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____23663 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____23671 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____23671
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____23680
                                                                  =
                                                                  let uu____23681
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____23681.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____23680
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____23687)
                                                                    -> hd1
                                                                | uu____23712
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____23716
                                                                =
                                                                let uu____23727
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____23727]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____23716)
                                                       | uu____23760 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____23765 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____23765 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____23785 ->
                                                     let uu____23794 =
                                                       let uu____23801 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____23801 cfg env
                                                        in
                                                     uu____23794 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____23812 = simp_t t  in
                      (match uu____23812 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____23821 ->
                      let uu____23844 = is_const_match tm1  in
                      (match uu____23844 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____23853 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____23863  ->
               (let uu____23865 = FStar_Syntax_Print.tag_of_term t  in
                let uu____23867 = FStar_Syntax_Print.term_to_string t  in
                let uu____23869 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____23877 =
                  let uu____23879 =
                    let uu____23882 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____23882
                     in
                  stack_to_string uu____23879  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____23865 uu____23867 uu____23869 uu____23877);
               (let uu____23907 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____23907
                then
                  let uu____23911 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____23911 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____23918 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____23920 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____23922 =
                          let uu____23924 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____23924
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____23918
                          uu____23920 uu____23922);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____23946 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____23954)::uu____23955 -> true
                | uu____23965 -> false)
              in
           if uu____23946
           then
             let uu____23968 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____23968 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____23982 =
                        let uu____23984 =
                          let uu____23986 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____23986  in
                        FStar_Util.string_of_int uu____23984  in
                      let uu____23993 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____23995 =
                        FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                      let uu____23997 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print4
                        "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                        uu____23982 uu____23993 uu____23995 uu____23997)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____24006,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24035  ->
                        let uu____24036 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24036);
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
                  let uu____24079 =
                    let uu___2783_24080 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2783_24080.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2783_24080.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____24079
              | (Arg (Univ uu____24083,uu____24084,uu____24085))::uu____24086
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____24090,uu____24091))::uu____24092 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____24108,uu____24109),aq,r))::stack1
                  when
                  let uu____24161 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24161 ->
                  let t2 =
                    let uu____24165 =
                      let uu____24170 =
                        let uu____24171 = closure_as_term cfg env_arg tm  in
                        (uu____24171, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____24170  in
                    uu____24165 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____24181),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24236  ->
                        let uu____24237 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____24237);
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
                     (let uu____24257 = FStar_ST.op_Bang m  in
                      match uu____24257 with
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
                      | FStar_Pervasives_Native.Some (uu____24345,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____24401 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____24406  ->
                         let uu____24407 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____24407);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____24417 =
                    let uu____24418 = FStar_Syntax_Subst.compress t1  in
                    uu____24418.FStar_Syntax_Syntax.n  in
                  (match uu____24417 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____24446 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____24446  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____24450  ->
                             let uu____24451 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____24451);
                        (let uu____24454 = FStar_List.tl stack  in
                         norm cfg env1 uu____24454 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____24455);
                          FStar_Syntax_Syntax.pos = uu____24456;
                          FStar_Syntax_Syntax.vars = uu____24457;_},(e,uu____24459)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____24498 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____24515 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____24515 with
                        | (hd1,args) ->
                            let uu____24558 =
                              let uu____24559 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____24559.FStar_Syntax_Syntax.n  in
                            (match uu____24558 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____24563 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____24563 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____24566;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____24567;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____24568;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____24570;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____24571;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____24572;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____24573;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____24609 -> fallback " (3)" ())
                             | uu____24613 -> fallback " (4)" ()))
                   | uu____24615 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____24641  ->
                        let uu____24642 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____24642);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____24653 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____24658  ->
                           let uu____24659 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____24661 =
                             let uu____24663 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____24693  ->
                                       match uu____24693 with
                                       | (p,uu____24704,uu____24705) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____24663
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____24659 uu____24661);
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
                                (fun uu___16_24727  ->
                                   match uu___16_24727 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____24731 -> false))
                            in
                         let steps =
                           let uu___2951_24734 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___2951_24734.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___2954_24741 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___2954_24741.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___2954_24741.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___2954_24741.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___2954_24741.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___2954_24741.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___2954_24741.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____24816 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____24847 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____24936  ->
                                       fun uu____24937  ->
                                         match (uu____24936, uu____24937)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____25087 =
                                               norm_pat env3 p1  in
                                             (match uu____25087 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____24847 with
                              | (pats1,env3) ->
                                  ((let uu___2982_25257 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___2982_25257.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___2986_25278 = x  in
                               let uu____25279 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2986_25278.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2986_25278.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25279
                               }  in
                             ((let uu___2989_25293 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___2989_25293.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___2993_25304 = x  in
                               let uu____25305 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2993_25304.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2993_25304.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25305
                               }  in
                             ((let uu___2996_25319 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___2996_25319.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3002_25335 = x  in
                               let uu____25336 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3002_25335.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3002_25335.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25336
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3006_25351 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3006_25351.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____25395 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____25425 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____25425 with
                                     | (p,wopt,e) ->
                                         let uu____25445 = norm_pat env1 p
                                            in
                                         (match uu____25445 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____25500 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____25500
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____25517 =
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
                         if uu____25517
                         then
                           norm
                             (let uu___3025_25524 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3027_25527 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3027_25527.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3025_25524.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3025_25524.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3025_25524.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3025_25524.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3025_25524.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3025_25524.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3025_25524.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3025_25524.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____25531 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____25531)
                       in
                    let rec is_cons head1 =
                      let uu____25557 =
                        let uu____25558 = FStar_Syntax_Subst.compress head1
                           in
                        uu____25558.FStar_Syntax_Syntax.n  in
                      match uu____25557 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____25563) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____25568 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____25570;
                            FStar_Syntax_Syntax.fv_delta = uu____25571;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____25573;
                            FStar_Syntax_Syntax.fv_delta = uu____25574;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____25575);_}
                          -> true
                      | uu____25583 -> false  in
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
                      let uu____25752 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____25752 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____25849 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____25891 ->
                                    let uu____25892 =
                                      let uu____25894 = is_cons head1  in
                                      Prims.op_Negation uu____25894  in
                                    FStar_Util.Inr uu____25892)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____25923 =
                                 let uu____25924 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____25924.FStar_Syntax_Syntax.n  in
                               (match uu____25923 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____25943 ->
                                    let uu____25944 =
                                      let uu____25946 = is_cons head1  in
                                      Prims.op_Negation uu____25946  in
                                    FStar_Util.Inr uu____25944))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____26037)::rest_a,(p1,uu____26040)::rest_p)
                          ->
                          let uu____26099 = matches_pat t2 p1  in
                          (match uu____26099 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____26152 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____26275 = matches_pat scrutinee1 p1  in
                          (match uu____26275 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____26321  ->
                                     let uu____26322 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____26324 =
                                       let uu____26326 =
                                         FStar_List.map
                                           (fun uu____26338  ->
                                              match uu____26338 with
                                              | (uu____26344,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____26326
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____26322 uu____26324);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____26380  ->
                                          match uu____26380 with
                                          | (bv,t2) ->
                                              let uu____26403 =
                                                let uu____26410 =
                                                  let uu____26413 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____26413
                                                   in
                                                let uu____26414 =
                                                  let uu____26415 =
                                                    let uu____26447 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____26447,
                                                      false)
                                                     in
                                                  Clos uu____26415  in
                                                (uu____26410, uu____26414)
                                                 in
                                              uu____26403 :: env2) env1 s
                                    in
                                 let uu____26540 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____26540)))
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
            (fun uu____26573  ->
               let uu____26574 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____26574);
          (let uu____26577 = is_nbe_request s  in
           if uu____26577
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____26583  ->
                   let uu____26584 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____26584);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____26590  ->
                   let uu____26591 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26591);
              (let uu____26594 =
                 FStar_Util.record_time (fun uu____26601  -> nbe_eval c s t)
                  in
               match uu____26594 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26610  ->
                         let uu____26611 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26613 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26611 uu____26613);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____26621  ->
                   let uu____26622 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____26622);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____26628  ->
                   let uu____26629 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26629);
              (let uu____26632 =
                 FStar_Util.record_time (fun uu____26639  -> norm c [] [] t)
                  in
               match uu____26632 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26654  ->
                         let uu____26655 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26657 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26655 uu____26657);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____26676 =
          let uu____26680 =
            let uu____26682 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____26682  in
          FStar_Pervasives_Native.Some uu____26680  in
        FStar_Profiling.profile
          (fun uu____26685  -> normalize_with_primitive_steps [] s e t)
          uu____26676 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____26707  ->
             let uu____26708 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____26708);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____26714  ->
             let uu____26715 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____26715);
        (let uu____26718 =
           FStar_Util.record_time (fun uu____26725  -> norm_comp cfg [] c)
            in
         match uu____26718 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____26740  ->
                   let uu____26741 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____26743 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____26741
                     uu____26743);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____26757 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____26757 [] u
  
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
      let uu____26779 = normalize steps env t  in
      FStar_TypeChecker_Env.non_informative env uu____26779
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____26791 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env t ->
          let uu___3195_26810 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3195_26810.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3195_26810.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____26817 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____26817
          then
            let ct1 =
              let uu____26821 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____26821 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____26828 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____26828
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3205_26835 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3205_26835.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3205_26835.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3205_26835.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c
                     in
                  let uu___3209_26837 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3209_26837.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3209_26837.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3209_26837.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3209_26837.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3212_26838 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3212_26838.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3212_26838.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____26841 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      let uu____26853 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____26853
      then
        let uu____26856 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____26856 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3220_26860 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3220_26860.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3220_26860.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3220_26860.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3227_26879  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3226_26882 ->
            ((let uu____26884 =
                let uu____26890 =
                  let uu____26892 = FStar_Util.message_of_exn uu___3226_26882
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26892
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26890)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____26884);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3237_26911  ->
             match () with
             | () ->
                 let uu____26912 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____26912 [] c) ()
        with
        | uu___3236_26921 ->
            ((let uu____26923 =
                let uu____26929 =
                  let uu____26931 = FStar_Util.message_of_exn uu___3236_26921
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26931
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26929)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____26923);
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
                   let uu____26980 =
                     let uu____26981 =
                       let uu____26988 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____26988)  in
                     FStar_Syntax_Syntax.Tm_refine uu____26981  in
                   mk uu____26980 t01.FStar_Syntax_Syntax.pos
               | uu____26993 -> t2)
          | uu____26994 -> t2  in
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
        let uu____27088 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27088 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27125 ->
                 let uu____27134 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27134 with
                  | (actuals,uu____27144,uu____27145) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27165 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27165 with
                         | (binders,args) ->
                             let uu____27176 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27176
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
      | uu____27191 ->
          let uu____27192 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27192 with
           | (head1,args) ->
               let uu____27235 =
                 let uu____27236 = FStar_Syntax_Subst.compress head1  in
                 uu____27236.FStar_Syntax_Syntax.n  in
               (match uu____27235 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____27257 =
                      let uu____27272 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____27272  in
                    (match uu____27257 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27312 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3307_27320 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3307_27320.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3307_27320.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3307_27320.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3307_27320.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3307_27320.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3307_27320.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3307_27320.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3307_27320.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3307_27320.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3307_27320.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3307_27320.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3307_27320.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3307_27320.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3307_27320.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3307_27320.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3307_27320.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3307_27320.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3307_27320.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3307_27320.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3307_27320.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3307_27320.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3307_27320.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3307_27320.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3307_27320.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3307_27320.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3307_27320.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3307_27320.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3307_27320.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3307_27320.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3307_27320.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3307_27320.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3307_27320.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3307_27320.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3307_27320.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3307_27320.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3307_27320.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3307_27320.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3307_27320.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3307_27320.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3307_27320.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3307_27320.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3307_27320.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____27312 with
                            | (uu____27323,ty,uu____27325) ->
                                eta_expand_with_type env t ty))
                | uu____27326 ->
                    let uu____27327 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3314_27335 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3314_27335.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3314_27335.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3314_27335.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3314_27335.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3314_27335.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3314_27335.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3314_27335.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3314_27335.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3314_27335.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3314_27335.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3314_27335.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3314_27335.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3314_27335.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3314_27335.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3314_27335.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3314_27335.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3314_27335.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3314_27335.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3314_27335.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3314_27335.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3314_27335.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3314_27335.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3314_27335.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3314_27335.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3314_27335.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3314_27335.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3314_27335.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3314_27335.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3314_27335.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3314_27335.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3314_27335.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3314_27335.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3314_27335.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3314_27335.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3314_27335.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3314_27335.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3314_27335.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3314_27335.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3314_27335.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3314_27335.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3314_27335.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3314_27335.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____27327 with
                     | (uu____27338,ty,uu____27340) ->
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
      let uu___3326_27422 = x  in
      let uu____27423 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3326_27422.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3326_27422.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27423
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27426 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27450 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27451 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27452 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27453 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27460 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27461 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27462 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3352_27496 = rc  in
          let uu____27497 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____27506 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3352_27496.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27497;
            FStar_Syntax_Syntax.residual_flags = uu____27506
          }  in
        let uu____27509 =
          let uu____27510 =
            let uu____27529 = elim_delayed_subst_binders bs  in
            let uu____27538 = elim_delayed_subst_term t2  in
            let uu____27541 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____27529, uu____27538, uu____27541)  in
          FStar_Syntax_Syntax.Tm_abs uu____27510  in
        mk1 uu____27509
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____27578 =
          let uu____27579 =
            let uu____27594 = elim_delayed_subst_binders bs  in
            let uu____27603 = elim_delayed_subst_comp c  in
            (uu____27594, uu____27603)  in
          FStar_Syntax_Syntax.Tm_arrow uu____27579  in
        mk1 uu____27578
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____27622 =
          let uu____27623 =
            let uu____27630 = elim_bv bv  in
            let uu____27631 = elim_delayed_subst_term phi  in
            (uu____27630, uu____27631)  in
          FStar_Syntax_Syntax.Tm_refine uu____27623  in
        mk1 uu____27622
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____27662 =
          let uu____27663 =
            let uu____27680 = elim_delayed_subst_term t2  in
            let uu____27683 = elim_delayed_subst_args args  in
            (uu____27680, uu____27683)  in
          FStar_Syntax_Syntax.Tm_app uu____27663  in
        mk1 uu____27662
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3374_27755 = p  in
              let uu____27756 =
                let uu____27757 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____27757  in
              {
                FStar_Syntax_Syntax.v = uu____27756;
                FStar_Syntax_Syntax.p =
                  (uu___3374_27755.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3378_27759 = p  in
              let uu____27760 =
                let uu____27761 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____27761  in
              {
                FStar_Syntax_Syntax.v = uu____27760;
                FStar_Syntax_Syntax.p =
                  (uu___3378_27759.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3384_27768 = p  in
              let uu____27769 =
                let uu____27770 =
                  let uu____27777 = elim_bv x  in
                  let uu____27778 = elim_delayed_subst_term t0  in
                  (uu____27777, uu____27778)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____27770  in
              {
                FStar_Syntax_Syntax.v = uu____27769;
                FStar_Syntax_Syntax.p =
                  (uu___3384_27768.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3390_27803 = p  in
              let uu____27804 =
                let uu____27805 =
                  let uu____27819 =
                    FStar_List.map
                      (fun uu____27845  ->
                         match uu____27845 with
                         | (x,b) ->
                             let uu____27862 = elim_pat x  in
                             (uu____27862, b)) pats
                     in
                  (fv, uu____27819)  in
                FStar_Syntax_Syntax.Pat_cons uu____27805  in
              {
                FStar_Syntax_Syntax.v = uu____27804;
                FStar_Syntax_Syntax.p =
                  (uu___3390_27803.FStar_Syntax_Syntax.p)
              }
          | uu____27877 -> p  in
        let elim_branch uu____27901 =
          match uu____27901 with
          | (pat,wopt,t3) ->
              let uu____27927 = elim_pat pat  in
              let uu____27930 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____27933 = elim_delayed_subst_term t3  in
              (uu____27927, uu____27930, uu____27933)
           in
        let uu____27938 =
          let uu____27939 =
            let uu____27962 = elim_delayed_subst_term t2  in
            let uu____27965 = FStar_List.map elim_branch branches  in
            (uu____27962, uu____27965)  in
          FStar_Syntax_Syntax.Tm_match uu____27939  in
        mk1 uu____27938
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28096 =
          match uu____28096 with
          | (tc,topt) ->
              let uu____28131 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28141 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28141
                | FStar_Util.Inr c ->
                    let uu____28143 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28143
                 in
              let uu____28144 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28131, uu____28144)
           in
        let uu____28153 =
          let uu____28154 =
            let uu____28181 = elim_delayed_subst_term t2  in
            let uu____28184 = elim_ascription a  in
            (uu____28181, uu____28184, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28154  in
        mk1 uu____28153
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3420_28247 = lb  in
          let uu____28248 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____28251 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3420_28247.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3420_28247.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28248;
            FStar_Syntax_Syntax.lbeff =
              (uu___3420_28247.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28251;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3420_28247.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3420_28247.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____28254 =
          let uu____28255 =
            let uu____28269 =
              let uu____28277 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____28277)  in
            let uu____28289 = elim_delayed_subst_term t2  in
            (uu____28269, uu____28289)  in
          FStar_Syntax_Syntax.Tm_let uu____28255  in
        mk1 uu____28254
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____28334 =
          let uu____28335 =
            let uu____28342 = elim_delayed_subst_term tm  in
            (uu____28342, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____28335  in
        mk1 uu____28334
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____28353 =
          let uu____28354 =
            let uu____28361 = elim_delayed_subst_term t2  in
            let uu____28364 = elim_delayed_subst_meta md  in
            (uu____28361, uu____28364)  in
          FStar_Syntax_Syntax.Tm_meta uu____28354  in
        mk1 uu____28353

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_28373  ->
         match uu___17_28373 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28377 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____28377
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
        let uu____28400 =
          let uu____28401 =
            let uu____28410 = elim_delayed_subst_term t  in
            (uu____28410, uopt)  in
          FStar_Syntax_Syntax.Total uu____28401  in
        mk1 uu____28400
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____28427 =
          let uu____28428 =
            let uu____28437 = elim_delayed_subst_term t  in
            (uu____28437, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____28428  in
        mk1 uu____28427
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3453_28446 = ct  in
          let uu____28447 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____28450 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____28461 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3453_28446.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3453_28446.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28447;
            FStar_Syntax_Syntax.effect_args = uu____28450;
            FStar_Syntax_Syntax.flags = uu____28461
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_28464  ->
    match uu___18_28464 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____28499 =
          let uu____28520 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____28529 = FStar_List.map elim_delayed_subst_args args  in
          (uu____28520, uu____28529)  in
        FStar_Syntax_Syntax.Meta_pattern uu____28499
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____28584 =
          let uu____28591 = elim_delayed_subst_term t  in (m, uu____28591)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____28584
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____28603 =
          let uu____28612 = elim_delayed_subst_term t  in
          (m1, m2, uu____28612)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____28603
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
      (fun uu____28645  ->
         match uu____28645 with
         | (t,q) ->
             let uu____28664 = elim_delayed_subst_term t  in (uu____28664, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____28692  ->
         match uu____28692 with
         | (x,q) ->
             let uu____28711 =
               let uu___3479_28712 = x  in
               let uu____28713 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3479_28712.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3479_28712.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____28713
               }  in
             (uu____28711, q)) bs

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
            | (uu____28821,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____28853,FStar_Util.Inl t) ->
                let uu____28875 =
                  let uu____28882 =
                    let uu____28883 =
                      let uu____28898 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____28898)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____28883  in
                  FStar_Syntax_Syntax.mk uu____28882  in
                uu____28875 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____28911 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____28911 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____28943 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29016 ->
                    let uu____29017 =
                      let uu____29026 =
                        let uu____29027 = FStar_Syntax_Subst.compress t4  in
                        uu____29027.FStar_Syntax_Syntax.n  in
                      (uu____29026, tc)  in
                    (match uu____29017 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29056) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29103) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29148,FStar_Util.Inl uu____29149) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29180 -> failwith "Impossible")
                 in
              (match uu____28943 with
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
          let uu____29319 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____29319 with
          | (univ_names1,binders1,tc) ->
              let uu____29393 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____29393)
  
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
          let uu____29447 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____29447 with
          | (univ_names1,binders1,tc) ->
              let uu____29521 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____29521)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____29563 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____29563 with
           | (univ_names1,binders1,typ1) ->
               let uu___3562_29603 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3562_29603.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3562_29603.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3562_29603.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3562_29603.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3562_29603.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3568_29618 = s  in
          let uu____29619 =
            let uu____29620 =
              let uu____29629 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29629, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29620  in
          {
            FStar_Syntax_Syntax.sigel = uu____29619;
            FStar_Syntax_Syntax.sigrng =
              (uu___3568_29618.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3568_29618.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3568_29618.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3568_29618.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3568_29618.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29648 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29648 with
           | (univ_names1,uu____29672,typ1) ->
               let uu___3582_29694 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3582_29694.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3582_29694.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3582_29694.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3582_29694.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3582_29694.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____29701 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29701 with
           | (univ_names1,uu____29725,typ1) ->
               let uu___3593_29747 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3593_29747.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3593_29747.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3593_29747.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3593_29747.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3593_29747.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____29777 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____29777 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____29802 =
                            let uu____29803 =
                              let uu____29804 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____29804  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____29803
                             in
                          elim_delayed_subst_term uu____29802  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3609_29807 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3609_29807.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3609_29807.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3609_29807.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3609_29807.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3612_29808 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3612_29808.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3612_29808.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3612_29808.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3612_29808.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3612_29808.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3616_29815 = s  in
          let uu____29816 =
            let uu____29817 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____29817  in
          {
            FStar_Syntax_Syntax.sigel = uu____29816;
            FStar_Syntax_Syntax.sigrng =
              (uu___3616_29815.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3616_29815.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3616_29815.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3616_29815.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3616_29815.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____29821 = elim_uvars_aux_t env us [] t  in
          (match uu____29821 with
           | (us1,uu____29845,t1) ->
               let uu___3627_29867 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3627_29867.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3627_29867.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3627_29867.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3627_29867.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3627_29867.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____29869 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____29869 with
           | (univs1,binders,uu____29888) ->
               let uu____29909 =
                 let uu____29914 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____29914 with
                 | (univs_opening,univs2) ->
                     let uu____29937 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____29937)
                  in
               (match uu____29909 with
                | (univs_opening,univs_closing) ->
                    let uu____29940 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____29946 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____29947 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____29946, uu____29947)  in
                    (match uu____29940 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____29973 =
                           match uu____29973 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____29991 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____29991 with
                                | (us1,t1) ->
                                    let uu____30002 =
                                      let uu____30011 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30016 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30011, uu____30016)  in
                                    (match uu____30002 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30039 =
                                           let uu____30048 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____30053 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____30048, uu____30053)  in
                                         (match uu____30039 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30077 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30077
                                                 in
                                              let uu____30078 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30078 with
                                               | (uu____30105,uu____30106,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30129 =
                                                       let uu____30130 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30130
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30129
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30139 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____30139 with
                           | (uu____30158,uu____30159,t1) -> t1  in
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
                             | uu____30235 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____30262 =
                               let uu____30263 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____30263.FStar_Syntax_Syntax.n  in
                             match uu____30262 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____30322 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____30356 =
                               let uu____30357 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____30357.FStar_Syntax_Syntax.n  in
                             match uu____30356 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____30380) ->
                                 let uu____30405 = destruct_action_body body
                                    in
                                 (match uu____30405 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____30454 ->
                                 let uu____30455 = destruct_action_body t  in
                                 (match uu____30455 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____30510 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____30510 with
                           | (action_univs,t) ->
                               let uu____30519 = destruct_action_typ_templ t
                                  in
                               (match uu____30519 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3711_30566 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3711_30566.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3711_30566.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3714_30568 = ed  in
                           let uu____30569 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____30570 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____30571 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3714_30568.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3714_30568.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____30569;
                             FStar_Syntax_Syntax.combinators = uu____30570;
                             FStar_Syntax_Syntax.actions = uu____30571;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3714_30568.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3717_30574 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3717_30574.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3717_30574.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3717_30574.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3717_30574.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3717_30574.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_30595 =
            match uu___19_30595 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30626 = elim_uvars_aux_t env us [] t  in
                (match uu____30626 with
                 | (us1,uu____30658,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3732_30689 = sub_eff  in
            let uu____30690 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____30693 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3732_30689.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3732_30689.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30690;
              FStar_Syntax_Syntax.lift = uu____30693
            }  in
          let uu___3735_30696 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3735_30696.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3735_30696.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3735_30696.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3735_30696.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3735_30696.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____30706 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____30706 with
           | (univ_names1,binders1,comp1) ->
               let uu___3748_30746 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3748_30746.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3748_30746.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3748_30746.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3748_30746.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3748_30746.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____30749 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____30750 -> s
  
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
        let uu____30799 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____30799 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____30821 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____30821 with
             | (uu____30828,head_def) ->
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
      let uu____30834 = FStar_Syntax_Util.head_and_args t  in
      match uu____30834 with
      | (head1,args) ->
          let uu____30879 =
            let uu____30880 = FStar_Syntax_Subst.compress head1  in
            uu____30880.FStar_Syntax_Syntax.n  in
          (match uu____30879 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____30887;
                  FStar_Syntax_Syntax.vars = uu____30888;_},us)
               -> aux fv us args
           | uu____30894 -> FStar_Pervasives_Native.None)
  