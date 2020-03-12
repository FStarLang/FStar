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
               | FStar_Syntax_Syntax.Tm_delayed uu____9719 ->
                   let uu____9742 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9742
               | uu____9745 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9755  ->
               let uu____9756 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9758 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9760 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9762 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9770 =
                 let uu____9772 =
                   let uu____9775 = firstn (Prims.of_int (4)) stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9775
                    in
                 stack_to_string uu____9772  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9756 uu____9758 uu____9760 uu____9762 uu____9770);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9803  ->
               let uu____9804 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9804);
          (let t_opt = is_wp_req_ens_commutation cfg env t1  in
           let uu____9810 = FStar_All.pipe_right t_opt FStar_Util.is_some  in
           if uu____9810
           then
             ((let uu____9817 =
                 FStar_All.pipe_left
                   (FStar_TypeChecker_Env.debug
                      cfg.FStar_TypeChecker_Cfg.tcenv)
                   (FStar_Options.Other "WPReqEns")
                  in
               if uu____9817
               then
                 let uu____9822 = FStar_Syntax_Print.term_to_string t1  in
                 let uu____9824 =
                   let uu____9826 =
                     FStar_All.pipe_right t_opt FStar_Util.must  in
                   FStar_All.pipe_right uu____9826
                     FStar_Syntax_Print.term_to_string
                    in
                 FStar_Util.print2
                   "Norm request identified as wp_req_ens commutation{, \n\nreduced %s \n\nto\n\n %s\n"
                   uu____9822 uu____9824
               else ());
              (let uu____9833 = FStar_All.pipe_right t_opt FStar_Util.must
                  in
               norm cfg env stack uu____9833))
           else
             (match t1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_unknown  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____9841  ->
                        let uu____9842 = FStar_Syntax_Print.term_to_string t1
                           in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____9842);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_constant uu____9845 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____9849  ->
                        let uu____9850 = FStar_Syntax_Print.term_to_string t1
                           in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____9850);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_name uu____9853 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____9857  ->
                        let uu____9858 = FStar_Syntax_Print.term_to_string t1
                           in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____9858);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_lazy uu____9861 ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____9865  ->
                        let uu____9866 = FStar_Syntax_Print.term_to_string t1
                           in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____9866);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = uu____9869;
                    FStar_Syntax_Syntax.fv_delta = uu____9870;
                    FStar_Syntax_Syntax.fv_qual =
                      FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Data_ctor );_}
                  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____9874  ->
                        let uu____9875 = FStar_Syntax_Print.term_to_string t1
                           in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____9875);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar
                  { FStar_Syntax_Syntax.fv_name = uu____9878;
                    FStar_Syntax_Syntax.fv_delta = uu____9879;
                    FStar_Syntax_Syntax.fv_qual =
                      FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor uu____9880);_}
                  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____9890  ->
                        let uu____9891 = FStar_Syntax_Print.term_to_string t1
                           in
                        FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                          uu____9891);
                   rebuild cfg env stack t1)
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                  let qninfo =
                    FStar_TypeChecker_Env.lookup_qname
                      cfg.FStar_TypeChecker_Cfg.tcenv lid
                     in
                  let uu____9897 =
                    FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
                  (match uu____9897 with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Delta_constant_at_level _9900)
                       when _9900 = Prims.int_zero ->
                       (FStar_TypeChecker_Cfg.log_unfolding cfg
                          (fun uu____9904  ->
                             let uu____9905 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                               uu____9905);
                        rebuild cfg env stack t1)
                   | uu____9908 ->
                       let uu____9911 =
                         decide_unfolding cfg env stack
                           t1.FStar_Syntax_Syntax.pos fv qninfo
                          in
                       (match uu____9911 with
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
                  let uu____9950 = closure_as_term cfg env t2  in
                  rebuild cfg env stack uu____9950
              | FStar_Syntax_Syntax.Tm_app (hd1,args) when
                  (should_consider_norm_requests cfg) &&
                    (let uu____9978 = is_norm_request hd1 args  in
                     uu____9978 = Norm_request_requires_rejig)
                  ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     FStar_Util.print_string "Rejigging norm request ... \n"
                   else ();
                   (let uu____9984 = rejig_norm_request hd1 args  in
                    norm cfg env stack uu____9984))
              | FStar_Syntax_Syntax.Tm_app (hd1,args) when
                  (should_consider_norm_requests cfg) &&
                    (let uu____10012 = is_norm_request hd1 args  in
                     uu____10012 = Norm_request_ready)
                  ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     FStar_Util.print_string "Potential norm request ... \n"
                   else ();
                   (let cfg' =
                      let uu___1265_10019 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (let uu___1267_10022 =
                             cfg.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               false;
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1267_10022.FStar_TypeChecker_Cfg.for_extraction)
                           });
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1265_10019.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1265_10019.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          [FStar_TypeChecker_Env.Unfold
                             FStar_Syntax_Syntax.delta_constant];
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1265_10019.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1265_10019.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1265_10019.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___1265_10019.FStar_TypeChecker_Cfg.reifying)
                      }  in
                    let uu____10029 =
                      get_norm_request cfg (norm cfg' env []) args  in
                    match uu____10029 with
                    | FStar_Pervasives_Native.None  ->
                        (if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           FStar_Util.print_string "Norm request None ... \n"
                         else ();
                         (let stack1 =
                            FStar_All.pipe_right stack
                              (FStar_List.fold_right
                                 (fun uu____10065  ->
                                    fun stack1  ->
                                      match uu____10065 with
                                      | (a,aq) ->
                                          let uu____10077 =
                                            let uu____10078 =
                                              let uu____10085 =
                                                let uu____10086 =
                                                  let uu____10118 =
                                                    FStar_Util.mk_ref
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  (env, a, uu____10118,
                                                    false)
                                                   in
                                                Clos uu____10086  in
                                              (uu____10085, aq,
                                                (t1.FStar_Syntax_Syntax.pos))
                                               in
                                            Arg uu____10078  in
                                          uu____10077 :: stack1) args)
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____10186  ->
                               let uu____10187 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length args)
                                  in
                               FStar_Util.print1 "\tPushed %s arguments\n"
                                 uu____10187);
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
                            let uu____10219 =
                              let uu____10221 =
                                let uu____10223 =
                                  FStar_Util.time_diff start fin  in
                                FStar_Pervasives_Native.snd uu____10223  in
                              FStar_Util.string_of_int uu____10221  in
                            let uu____10230 =
                              FStar_Syntax_Print.term_to_string tm'  in
                            let uu____10232 =
                              FStar_TypeChecker_Cfg.cfg_to_string cfg'1  in
                            let uu____10234 =
                              FStar_Syntax_Print.term_to_string tm_norm  in
                            FStar_Util.print4
                              "NBE result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                              uu____10219 uu____10230 uu____10232 uu____10234)
                         else ();
                         rebuild cfg env stack tm_norm)
                    | FStar_Pervasives_Native.Some (s,tm) ->
                        let delta_level =
                          let uu____10254 =
                            FStar_All.pipe_right s
                              (FStar_Util.for_some
                                 (fun uu___13_10261  ->
                                    match uu___13_10261 with
                                    | FStar_TypeChecker_Env.UnfoldUntil
                                        uu____10263 -> true
                                    | FStar_TypeChecker_Env.UnfoldOnly
                                        uu____10265 -> true
                                    | FStar_TypeChecker_Env.UnfoldFully
                                        uu____10269 -> true
                                    | uu____10273 -> false))
                             in
                          if uu____10254
                          then
                            [FStar_TypeChecker_Env.Unfold
                               FStar_Syntax_Syntax.delta_constant]
                          else [FStar_TypeChecker_Env.NoDelta]  in
                        let cfg'1 =
                          let uu___1305_10281 = cfg  in
                          let uu____10282 =
                            let uu___1307_10283 =
                              FStar_TypeChecker_Cfg.to_fsteps s  in
                            {
                              FStar_TypeChecker_Cfg.beta =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.beta);
                              FStar_TypeChecker_Cfg.iota =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.iota);
                              FStar_TypeChecker_Cfg.zeta =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.zeta);
                              FStar_TypeChecker_Cfg.weak =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.weak);
                              FStar_TypeChecker_Cfg.hnf =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.hnf);
                              FStar_TypeChecker_Cfg.primops =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.primops);
                              FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                              FStar_TypeChecker_Cfg.unfold_until =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.unfold_until);
                              FStar_TypeChecker_Cfg.unfold_only =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.unfold_only);
                              FStar_TypeChecker_Cfg.unfold_fully =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.unfold_fully);
                              FStar_TypeChecker_Cfg.unfold_attr =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.unfold_attr);
                              FStar_TypeChecker_Cfg.unfold_tac =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.unfold_tac);
                              FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                              FStar_TypeChecker_Cfg.simplify =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.simplify);
                              FStar_TypeChecker_Cfg.erase_universes =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.erase_universes);
                              FStar_TypeChecker_Cfg.allow_unbound_universes =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.allow_unbound_universes);
                              FStar_TypeChecker_Cfg.reify_ =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.reify_);
                              FStar_TypeChecker_Cfg.compress_uvars =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.compress_uvars);
                              FStar_TypeChecker_Cfg.no_full_norm =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.no_full_norm);
                              FStar_TypeChecker_Cfg.check_no_uvars =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.check_no_uvars);
                              FStar_TypeChecker_Cfg.unmeta =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.unmeta);
                              FStar_TypeChecker_Cfg.unascribe =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.unascribe);
                              FStar_TypeChecker_Cfg.in_full_norm_request =
                                true;
                              FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                              FStar_TypeChecker_Cfg.nbe_step =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.nbe_step);
                              FStar_TypeChecker_Cfg.for_extraction =
                                (uu___1307_10283.FStar_TypeChecker_Cfg.for_extraction)
                            }  in
                          {
                            FStar_TypeChecker_Cfg.steps = uu____10282;
                            FStar_TypeChecker_Cfg.tcenv =
                              (uu___1305_10281.FStar_TypeChecker_Cfg.tcenv);
                            FStar_TypeChecker_Cfg.debug =
                              (uu___1305_10281.FStar_TypeChecker_Cfg.debug);
                            FStar_TypeChecker_Cfg.delta_level = delta_level;
                            FStar_TypeChecker_Cfg.primitive_steps =
                              (uu___1305_10281.FStar_TypeChecker_Cfg.primitive_steps);
                            FStar_TypeChecker_Cfg.strong =
                              (uu___1305_10281.FStar_TypeChecker_Cfg.strong);
                            FStar_TypeChecker_Cfg.memoize_lazy =
                              (uu___1305_10281.FStar_TypeChecker_Cfg.memoize_lazy);
                            FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                            FStar_TypeChecker_Cfg.reifying =
                              (uu___1305_10281.FStar_TypeChecker_Cfg.reifying)
                          }  in
                        let stack' =
                          let tail1 = (Cfg cfg) :: stack  in
                          if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                          then
                            let uu____10291 =
                              let uu____10292 =
                                let uu____10297 = FStar_Util.now ()  in
                                (tm, uu____10297)  in
                              Debug uu____10292  in
                            uu____10291 :: tail1
                          else tail1  in
                        norm cfg'1 env stack' tm))
              | FStar_Syntax_Syntax.Tm_type u ->
                  let u1 = norm_universe cfg env u  in
                  let uu____10302 =
                    mk (FStar_Syntax_Syntax.Tm_type u1)
                      t1.FStar_Syntax_Syntax.pos
                     in
                  rebuild cfg env stack uu____10302
              | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                  if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                  then norm cfg env stack t'
                  else
                    (let us1 =
                       let uu____10313 =
                         let uu____10320 =
                           FStar_List.map (norm_universe cfg env) us  in
                         (uu____10320, (t1.FStar_Syntax_Syntax.pos))  in
                       UnivArgs uu____10313  in
                     let stack1 = us1 :: stack  in norm cfg env stack1 t')
              | FStar_Syntax_Syntax.Tm_bvar x ->
                  let uu____10329 = lookup_bvar env x  in
                  (match uu____10329 with
                   | Univ uu____10330 ->
                       failwith
                         "Impossible: term variable is bound to a universe"
                   | Dummy  -> failwith "Term variable not found"
                   | Clos (env1,t0,r,fix) ->
                       if
                         (Prims.op_Negation fix) ||
                           (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                       then
                         let uu____10384 = FStar_ST.op_Bang r  in
                         (match uu____10384 with
                          | FStar_Pervasives_Native.Some (env2,t') ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10480  ->
                                    let uu____10481 =
                                      FStar_Syntax_Print.term_to_string t1
                                       in
                                    let uu____10483 =
                                      FStar_Syntax_Print.term_to_string t'
                                       in
                                    FStar_Util.print2
                                      "Lazy hit: %s cached to %s\n"
                                      uu____10481 uu____10483);
                               (let uu____10486 = maybe_weakly_reduced t'  in
                                if uu____10486
                                then
                                  match stack with
                                  | [] when
                                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                        ||
                                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                      -> rebuild cfg env2 stack t'
                                  | uu____10489 -> norm cfg env2 stack t'
                                else rebuild cfg env2 stack t'))
                          | FStar_Pervasives_Native.None  ->
                              norm cfg env1 ((MemoLazy r) :: stack) t0)
                       else norm cfg env1 stack t0)
              | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
                  (match stack with
                   | (UnivArgs uu____10533)::uu____10534 ->
                       failwith
                         "Ill-typed term: universes cannot be applied to term abstraction"
                   | (Arg (c,uu____10545,uu____10546))::stack_rest ->
                       (match c with
                        | Univ uu____10550 ->
                            norm cfg ((FStar_Pervasives_Native.None, c) ::
                              env) stack_rest t1
                        | uu____10559 ->
                            (match bs with
                             | [] -> failwith "Impossible"
                             | b::[] ->
                                 (FStar_TypeChecker_Cfg.log cfg
                                    (fun uu____10589  ->
                                       let uu____10590 = closure_to_string c
                                          in
                                       FStar_Util.print1 "\tShifted %s\n"
                                         uu____10590);
                                  norm cfg
                                    (((FStar_Pervasives_Native.Some b), c) ::
                                    env) stack_rest body)
                             | b::tl1 ->
                                 (FStar_TypeChecker_Cfg.log cfg
                                    (fun uu____10626  ->
                                       let uu____10627 = closure_to_string c
                                          in
                                       FStar_Util.print1 "\tShifted %s\n"
                                         uu____10627);
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
                          (fun uu____10675  ->
                             let uu____10676 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.print1 "\tSet memo %s\n" uu____10676);
                        norm cfg env stack1 t1)
                   | (Match uu____10679)::uu____10680 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____10695 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____10695 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____10731  -> dummy :: env1)
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
                                             let uu____10775 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____10775)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1425_10783 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1425_10783.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1425_10783.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____10784 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10790  ->
                                    let uu____10791 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____10791);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1432_10806 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1432_10806.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1432_10806.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1432_10806.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1432_10806.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1432_10806.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1432_10806.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1432_10806.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1432_10806.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Debug uu____10810)::uu____10811 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____10822 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____10822 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____10858  -> dummy :: env1)
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
                                             let uu____10902 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____10902)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1425_10910 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1425_10910.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1425_10910.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____10911 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10917  ->
                                    let uu____10918 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____10918);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1432_10933 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1432_10933.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1432_10933.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1432_10933.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1432_10933.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1432_10933.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1432_10933.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1432_10933.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1432_10933.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Meta uu____10937)::uu____10938 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____10951 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____10951 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____10987  -> dummy :: env1)
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
                                             let uu____11031 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____11031)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1425_11039 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1425_11039.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1425_11039.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____11040 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11046  ->
                                    let uu____11047 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____11047);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1432_11062 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1432_11062.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1432_11062.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1432_11062.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1432_11062.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1432_11062.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1432_11062.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1432_11062.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1432_11062.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Let uu____11066)::uu____11067 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____11082 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____11082 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____11118  -> dummy :: env1)
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
                                             let uu____11162 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____11162)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1425_11170 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1425_11170.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1425_11170.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____11171 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11177  ->
                                    let uu____11178 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____11178);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1432_11193 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1432_11193.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1432_11193.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1432_11193.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1432_11193.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1432_11193.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1432_11193.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1432_11193.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1432_11193.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (App uu____11197)::uu____11198 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____11213 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____11213 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____11249  -> dummy :: env1)
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
                                             let uu____11293 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____11293)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1425_11301 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1425_11301.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1425_11301.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____11302 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11308  ->
                                    let uu____11309 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____11309);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1432_11324 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1432_11324.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1432_11324.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1432_11324.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1432_11324.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1432_11324.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1432_11324.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1432_11324.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1432_11324.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1)))
                   | (Abs uu____11328)::uu____11329 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                       then
                         let t2 = closure_as_term cfg env t1  in
                         rebuild cfg env stack t2
                       else
                         (let uu____11348 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____11348 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____11384  -> dummy :: env1)
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
                                             let uu____11428 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____11428)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1425_11436 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1425_11436.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1425_11436.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____11437 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11443  ->
                                    let uu____11444 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____11444);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1432_11459 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1432_11459.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1432_11459.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1432_11459.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1432_11459.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1432_11459.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1432_11459.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1432_11459.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1432_11459.FStar_TypeChecker_Cfg.reifying)
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
                         (let uu____11467 =
                            FStar_Syntax_Subst.open_term' bs body  in
                          match uu____11467 with
                          | (bs1,body1,opening) ->
                              let env' =
                                FStar_All.pipe_right bs1
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____11503  -> dummy :: env1)
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
                                             let uu____11547 =
                                               FStar_Syntax_Subst.subst
                                                 opening t2
                                                in
                                             norm cfg env' [] uu____11547)
                                      else
                                        FStar_Util.map_opt
                                          rc.FStar_Syntax_Syntax.residual_typ
                                          (FStar_Syntax_Subst.subst opening)
                                       in
                                    FStar_Pervasives_Native.Some
                                      (let uu___1425_11555 = rc  in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1425_11555.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           rct;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1425_11555.FStar_Syntax_Syntax.residual_flags)
                                       })
                                | uu____11556 -> lopt  in
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____11562  ->
                                    let uu____11563 =
                                      FStar_All.pipe_left
                                        FStar_Util.string_of_int
                                        (FStar_List.length bs1)
                                       in
                                    FStar_Util.print1
                                      "\tShifted %s dummies\n" uu____11563);
                               (let stack1 = (Cfg cfg) :: stack  in
                                let cfg1 =
                                  let uu___1432_11578 = cfg  in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1432_11578.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv =
                                      (uu___1432_11578.FStar_TypeChecker_Cfg.tcenv);
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1432_11578.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1432_11578.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1432_11578.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong = true;
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1432_11578.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1432_11578.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1432_11578.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                norm cfg1 env'
                                  ((Abs
                                      (env, bs1, env', lopt1,
                                        (t1.FStar_Syntax_Syntax.pos))) ::
                                  stack1) body1))))
              | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                  let strict_args =
                    let uu____11614 =
                      let uu____11615 = FStar_Syntax_Util.un_uinst head1  in
                      uu____11615.FStar_Syntax_Syntax.n  in
                    match uu____11614 with
                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                        FStar_TypeChecker_Env.fv_has_strict_args
                          cfg.FStar_TypeChecker_Cfg.tcenv fv
                    | uu____11624 -> FStar_Pervasives_Native.None  in
                  (match strict_args with
                   | FStar_Pervasives_Native.None  ->
                       let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____11645  ->
                                 fun stack1  ->
                                   match uu____11645 with
                                   | (a,aq) ->
                                       let uu____11657 =
                                         let uu____11658 =
                                           let uu____11665 =
                                             let uu____11666 =
                                               let uu____11698 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____11698, false)
                                                in
                                             Clos uu____11666  in
                                           (uu____11665, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____11658  in
                                       uu____11657 :: stack1) args)
                          in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____11766  ->
                             let uu____11767 =
                               FStar_All.pipe_left FStar_Util.string_of_int
                                 (FStar_List.length args)
                                in
                             FStar_Util.print1 "\tPushed %s arguments\n"
                               uu____11767);
                        norm cfg env stack1 head1)
                   | FStar_Pervasives_Native.Some strict_args1 ->
                       let norm_args =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun uu____11818  ->
                                 match uu____11818 with
                                 | (a,i) ->
                                     let uu____11829 = norm cfg env [] a  in
                                     (uu____11829, i)))
                          in
                       let norm_args_len = FStar_List.length norm_args  in
                       let uu____11835 =
                         FStar_All.pipe_right strict_args1
                           (FStar_List.for_all
                              (fun i  ->
                                 if i >= norm_args_len
                                 then false
                                 else
                                   (let uu____11850 =
                                      FStar_List.nth norm_args i  in
                                    match uu____11850 with
                                    | (arg_i,uu____11861) ->
                                        let uu____11862 =
                                          FStar_Syntax_Util.head_and_args
                                            arg_i
                                           in
                                        (match uu____11862 with
                                         | (head2,uu____11881) ->
                                             let uu____11906 =
                                               let uu____11907 =
                                                 FStar_Syntax_Util.un_uinst
                                                   head2
                                                  in
                                               uu____11907.FStar_Syntax_Syntax.n
                                                in
                                             (match uu____11906 with
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____11911 -> true
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv ->
                                                  let uu____11914 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Env.is_datacon
                                                    cfg.FStar_TypeChecker_Cfg.tcenv
                                                    uu____11914
                                              | uu____11915 -> false)))))
                          in
                       if uu____11835
                       then
                         let stack1 =
                           FStar_All.pipe_right stack
                             (FStar_List.fold_right
                                (fun uu____11932  ->
                                   fun stack1  ->
                                     match uu____11932 with
                                     | (a,aq) ->
                                         let uu____11944 =
                                           let uu____11945 =
                                             let uu____11952 =
                                               let uu____11953 =
                                                 let uu____11985 =
                                                   FStar_Util.mk_ref
                                                     (FStar_Pervasives_Native.Some
                                                        ([], a))
                                                    in
                                                 (env, a, uu____11985, false)
                                                  in
                                               Clos uu____11953  in
                                             (uu____11952, aq,
                                               (t1.FStar_Syntax_Syntax.pos))
                                              in
                                           Arg uu____11945  in
                                         uu____11944 :: stack1) norm_args)
                            in
                         (FStar_TypeChecker_Cfg.log cfg
                            (fun uu____12067  ->
                               let uu____12068 =
                                 FStar_All.pipe_left FStar_Util.string_of_int
                                   (FStar_List.length args)
                                  in
                               FStar_Util.print1 "\tPushed %s arguments\n"
                                 uu____12068);
                          norm cfg env stack1 head1)
                       else
                         (let head2 = closure_as_term cfg env head1  in
                          let term =
                            FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                              FStar_Pervasives_Native.None
                              t1.FStar_Syntax_Syntax.pos
                             in
                          rebuild cfg env stack term))
              | FStar_Syntax_Syntax.Tm_refine (x,uu____12088) when
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
                                ((let uu___1494_12133 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1494_12133.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1494_12133.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = t_x
                                  }), f)) t1.FStar_Syntax_Syntax.pos
                            in
                         rebuild cfg env stack t2
                     | uu____12134 ->
                         let uu____12149 = closure_as_term cfg env t1  in
                         rebuild cfg env stack uu____12149)
                  else
                    (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                     let uu____12153 =
                       FStar_Syntax_Subst.open_term
                         [(x, FStar_Pervasives_Native.None)] f
                        in
                     match uu____12153 with
                     | (closing,f1) ->
                         let f2 = norm cfg (dummy :: env) [] f1  in
                         let t2 =
                           let uu____12184 =
                             let uu____12185 =
                               let uu____12192 =
                                 FStar_Syntax_Subst.close closing f2  in
                               ((let uu___1503_12198 = x  in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1503_12198.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___1503_12198.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = t_x
                                 }), uu____12192)
                                in
                             FStar_Syntax_Syntax.Tm_refine uu____12185  in
                           mk uu____12184 t1.FStar_Syntax_Syntax.pos  in
                         rebuild cfg env stack t2)
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                  if
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                  then
                    let uu____12222 = closure_as_term cfg env t1  in
                    rebuild cfg env stack uu____12222
                  else
                    (let uu____12225 = FStar_Syntax_Subst.open_comp bs c  in
                     match uu____12225 with
                     | (bs1,c1) ->
                         let c2 =
                           let uu____12233 =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12259  -> dummy :: env1) env)
                              in
                           norm_comp cfg uu____12233 c1  in
                         let t2 =
                           let uu____12283 = norm_binders cfg env bs1  in
                           FStar_Syntax_Util.arrow uu____12283 c2  in
                         rebuild cfg env stack t2)
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
                  -> norm cfg env stack t11
              | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
                  (match stack with
                   | (Match uu____12396)::uu____12397 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____12410  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (Arg uu____12412)::uu____12413 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____12424  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (App
                       (uu____12426,{
                                      FStar_Syntax_Syntax.n =
                                        FStar_Syntax_Syntax.Tm_constant
                                        (FStar_Const.Const_reify );
                                      FStar_Syntax_Syntax.pos = uu____12427;
                                      FStar_Syntax_Syntax.vars = uu____12428;_},uu____12429,uu____12430))::uu____12431
                       when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____12438  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | (MemoLazy uu____12440)::uu____12441 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                       ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____12452  ->
                             FStar_Util.print_string
                               "+++ Dropping ascription \n");
                        norm cfg env stack t11)
                   | uu____12454 ->
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____12457  ->
                             FStar_Util.print_string
                               "+++ Keeping ascription \n");
                        (let t12 = norm cfg env [] t11  in
                         FStar_TypeChecker_Cfg.log cfg
                           (fun uu____12462  ->
                              FStar_Util.print_string
                                "+++ Normalizing ascription \n");
                         (let tc1 =
                            match tc with
                            | FStar_Util.Inl t2 ->
                                let uu____12488 = norm cfg env [] t2  in
                                FStar_Util.Inl uu____12488
                            | FStar_Util.Inr c ->
                                let uu____12502 = norm_comp cfg env c  in
                                FStar_Util.Inr uu____12502
                             in
                          let tacopt1 =
                            FStar_Util.map_opt tacopt (norm cfg env [])  in
                          match stack with
                          | (Cfg cfg1)::stack1 ->
                              let t2 =
                                let uu____12525 =
                                  let uu____12526 =
                                    let uu____12553 =
                                      FStar_Syntax_Util.unascribe t12  in
                                    (uu____12553, (tc1, tacopt1), l)  in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____12526
                                   in
                                mk uu____12525 t1.FStar_Syntax_Syntax.pos  in
                              norm cfg1 env stack1 t2
                          | uu____12588 ->
                              let uu____12589 =
                                let uu____12590 =
                                  let uu____12591 =
                                    let uu____12618 =
                                      FStar_Syntax_Util.unascribe t12  in
                                    (uu____12618, (tc1, tacopt1), l)  in
                                  FStar_Syntax_Syntax.Tm_ascribed uu____12591
                                   in
                                mk uu____12590 t1.FStar_Syntax_Syntax.pos  in
                              rebuild cfg env stack uu____12589))))
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
                      let uu___1582_12696 = cfg  in
                      {
                        FStar_TypeChecker_Cfg.steps =
                          (let uu___1584_12699 =
                             cfg.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak = true;
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1584_12699.FStar_TypeChecker_Cfg.for_extraction)
                           });
                        FStar_TypeChecker_Cfg.tcenv =
                          (uu___1582_12696.FStar_TypeChecker_Cfg.tcenv);
                        FStar_TypeChecker_Cfg.debug =
                          (uu___1582_12696.FStar_TypeChecker_Cfg.debug);
                        FStar_TypeChecker_Cfg.delta_level =
                          (uu___1582_12696.FStar_TypeChecker_Cfg.delta_level);
                        FStar_TypeChecker_Cfg.primitive_steps =
                          (uu___1582_12696.FStar_TypeChecker_Cfg.primitive_steps);
                        FStar_TypeChecker_Cfg.strong =
                          (uu___1582_12696.FStar_TypeChecker_Cfg.strong);
                        FStar_TypeChecker_Cfg.memoize_lazy =
                          (uu___1582_12696.FStar_TypeChecker_Cfg.memoize_lazy);
                        FStar_TypeChecker_Cfg.normalize_pure_lets =
                          (uu___1582_12696.FStar_TypeChecker_Cfg.normalize_pure_lets);
                        FStar_TypeChecker_Cfg.reifying =
                          (uu___1582_12696.FStar_TypeChecker_Cfg.reifying)
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
                            let uu____12740 =
                              FStar_Syntax_Subst.univ_var_opening
                                lb.FStar_Syntax_Syntax.lbunivs
                               in
                            match uu____12740 with
                            | (openings,lbunivs) ->
                                let cfg1 =
                                  let uu___1597_12760 = cfg  in
                                  let uu____12761 =
                                    FStar_TypeChecker_Env.push_univ_vars
                                      cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                     in
                                  {
                                    FStar_TypeChecker_Cfg.steps =
                                      (uu___1597_12760.FStar_TypeChecker_Cfg.steps);
                                    FStar_TypeChecker_Cfg.tcenv = uu____12761;
                                    FStar_TypeChecker_Cfg.debug =
                                      (uu___1597_12760.FStar_TypeChecker_Cfg.debug);
                                    FStar_TypeChecker_Cfg.delta_level =
                                      (uu___1597_12760.FStar_TypeChecker_Cfg.delta_level);
                                    FStar_TypeChecker_Cfg.primitive_steps =
                                      (uu___1597_12760.FStar_TypeChecker_Cfg.primitive_steps);
                                    FStar_TypeChecker_Cfg.strong =
                                      (uu___1597_12760.FStar_TypeChecker_Cfg.strong);
                                    FStar_TypeChecker_Cfg.memoize_lazy =
                                      (uu___1597_12760.FStar_TypeChecker_Cfg.memoize_lazy);
                                    FStar_TypeChecker_Cfg.normalize_pure_lets
                                      =
                                      (uu___1597_12760.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                    FStar_TypeChecker_Cfg.reifying =
                                      (uu___1597_12760.FStar_TypeChecker_Cfg.reifying)
                                  }  in
                                let norm1 t2 =
                                  let uu____12768 =
                                    let uu____12769 =
                                      FStar_Syntax_Subst.subst openings t2
                                       in
                                    norm cfg1 env [] uu____12769  in
                                  FStar_Syntax_Subst.close_univ_vars lbunivs
                                    uu____12768
                                   in
                                let lbtyp =
                                  norm1 lb.FStar_Syntax_Syntax.lbtyp  in
                                let lbdef =
                                  norm1 lb.FStar_Syntax_Syntax.lbdef  in
                                let uu___1604_12772 = lb  in
                                {
                                  FStar_Syntax_Syntax.lbname =
                                    (uu___1604_12772.FStar_Syntax_Syntax.lbname);
                                  FStar_Syntax_Syntax.lbunivs = lbunivs;
                                  FStar_Syntax_Syntax.lbtyp = lbtyp;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1604_12772.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = lbdef;
                                  FStar_Syntax_Syntax.lbattrs =
                                    (uu___1604_12772.FStar_Syntax_Syntax.lbattrs);
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1604_12772.FStar_Syntax_Syntax.lbpos)
                                }))
                     in
                  let uu____12773 =
                    mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                      t1.FStar_Syntax_Syntax.pos
                     in
                  rebuild cfg env stack uu____12773
              | FStar_Syntax_Syntax.Tm_let
                  ((uu____12786,{
                                  FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                    uu____12787;
                                  FStar_Syntax_Syntax.lbunivs = uu____12788;
                                  FStar_Syntax_Syntax.lbtyp = uu____12789;
                                  FStar_Syntax_Syntax.lbeff = uu____12790;
                                  FStar_Syntax_Syntax.lbdef = uu____12791;
                                  FStar_Syntax_Syntax.lbattrs = uu____12792;
                                  FStar_Syntax_Syntax.lbpos = uu____12793;_}::uu____12794),uu____12795)
                  -> rebuild cfg env stack t1
              | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                  let uu____12840 =
                    FStar_TypeChecker_Cfg.should_reduce_local_let cfg lb  in
                  if uu____12840
                  then
                    let binder =
                      let uu____12844 =
                        FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                      FStar_Syntax_Syntax.mk_binder uu____12844  in
                    let env1 =
                      let uu____12854 =
                        let uu____12861 =
                          let uu____12862 =
                            let uu____12894 =
                              FStar_Util.mk_ref FStar_Pervasives_Native.None
                               in
                            (env, (lb.FStar_Syntax_Syntax.lbdef),
                              uu____12894, false)
                             in
                          Clos uu____12862  in
                        ((FStar_Pervasives_Native.Some binder), uu____12861)
                         in
                      uu____12854 :: env  in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12969  ->
                          FStar_Util.print_string "+++ Reducing Tm_let\n");
                     norm cfg env1 stack body)
                  else
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12976  ->
                            FStar_Util.print_string
                              "+++ Not touching Tm_let\n");
                       (let uu____12978 = closure_as_term cfg env t1  in
                        rebuild cfg env stack uu____12978))
                    else
                      (let uu____12981 =
                         let uu____12986 =
                           let uu____12987 =
                             let uu____12994 =
                               FStar_All.pipe_right
                                 lb.FStar_Syntax_Syntax.lbname
                                 FStar_Util.left
                                in
                             FStar_All.pipe_right uu____12994
                               FStar_Syntax_Syntax.mk_binder
                              in
                           [uu____12987]  in
                         FStar_Syntax_Subst.open_term uu____12986 body  in
                       match uu____12981 with
                       | (bs,body1) ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____13021  ->
                                 FStar_Util.print_string
                                   "+++ Normalizing Tm_let -- type");
                            (let ty =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbname =
                               let x =
                                 let uu____13030 = FStar_List.hd bs  in
                                 FStar_Pervasives_Native.fst uu____13030  in
                               FStar_Util.Inl
                                 (let uu___1645_13046 = x  in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1645_13046.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1645_13046.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  })
                                in
                             FStar_TypeChecker_Cfg.log cfg
                               (fun uu____13049  ->
                                  FStar_Util.print_string
                                    "+++ Normalizing Tm_let -- definiens\n");
                             (let lb1 =
                                let uu___1650_13052 = lb  in
                                let uu____13053 =
                                  norm cfg env []
                                    lb.FStar_Syntax_Syntax.lbdef
                                   in
                                let uu____13056 =
                                  FStar_List.map (norm cfg env [])
                                    lb.FStar_Syntax_Syntax.lbattrs
                                   in
                                {
                                  FStar_Syntax_Syntax.lbname = lbname;
                                  FStar_Syntax_Syntax.lbunivs =
                                    (uu___1650_13052.FStar_Syntax_Syntax.lbunivs);
                                  FStar_Syntax_Syntax.lbtyp = ty;
                                  FStar_Syntax_Syntax.lbeff =
                                    (uu___1650_13052.FStar_Syntax_Syntax.lbeff);
                                  FStar_Syntax_Syntax.lbdef = uu____13053;
                                  FStar_Syntax_Syntax.lbattrs = uu____13056;
                                  FStar_Syntax_Syntax.lbpos =
                                    (uu___1650_13052.FStar_Syntax_Syntax.lbpos)
                                }  in
                              let env' =
                                FStar_All.pipe_right bs
                                  (FStar_List.fold_left
                                     (fun env1  ->
                                        fun uu____13091  -> dummy :: env1)
                                     env)
                                 in
                              let stack1 = (Cfg cfg) :: stack  in
                              let cfg1 =
                                let uu___1657_13116 = cfg  in
                                {
                                  FStar_TypeChecker_Cfg.steps =
                                    (uu___1657_13116.FStar_TypeChecker_Cfg.steps);
                                  FStar_TypeChecker_Cfg.tcenv =
                                    (uu___1657_13116.FStar_TypeChecker_Cfg.tcenv);
                                  FStar_TypeChecker_Cfg.debug =
                                    (uu___1657_13116.FStar_TypeChecker_Cfg.debug);
                                  FStar_TypeChecker_Cfg.delta_level =
                                    (uu___1657_13116.FStar_TypeChecker_Cfg.delta_level);
                                  FStar_TypeChecker_Cfg.primitive_steps =
                                    (uu___1657_13116.FStar_TypeChecker_Cfg.primitive_steps);
                                  FStar_TypeChecker_Cfg.strong = true;
                                  FStar_TypeChecker_Cfg.memoize_lazy =
                                    (uu___1657_13116.FStar_TypeChecker_Cfg.memoize_lazy);
                                  FStar_TypeChecker_Cfg.normalize_pure_lets =
                                    (uu___1657_13116.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                  FStar_TypeChecker_Cfg.reifying =
                                    (uu___1657_13116.FStar_TypeChecker_Cfg.reifying)
                                }  in
                              FStar_TypeChecker_Cfg.log cfg1
                                (fun uu____13120  ->
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
                  let uu____13141 = FStar_Syntax_Subst.open_let_rec lbs body
                     in
                  (match uu____13141 with
                   | (lbs1,body1) ->
                       let lbs2 =
                         FStar_List.map
                           (fun lb  ->
                              let ty =
                                norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp
                                 in
                              let lbname =
                                let uu____13177 =
                                  let uu___1673_13178 =
                                    FStar_Util.left
                                      lb.FStar_Syntax_Syntax.lbname
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___1673_13178.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___1673_13178.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = ty
                                  }  in
                                FStar_Util.Inl uu____13177  in
                              let uu____13179 =
                                FStar_Syntax_Util.abs_formals
                                  lb.FStar_Syntax_Syntax.lbdef
                                 in
                              match uu____13179 with
                              | (xs,def_body,lopt) ->
                                  let xs1 = norm_binders cfg env xs  in
                                  let env1 =
                                    let uu____13205 =
                                      FStar_List.map
                                        (fun uu____13227  -> dummy) xs1
                                       in
                                    let uu____13234 =
                                      let uu____13243 =
                                        FStar_List.map
                                          (fun uu____13259  -> dummy) lbs1
                                         in
                                      FStar_List.append uu____13243 env  in
                                    FStar_List.append uu____13205 uu____13234
                                     in
                                  let def_body1 = norm cfg env1 [] def_body
                                     in
                                  let lopt1 =
                                    match lopt with
                                    | FStar_Pervasives_Native.Some rc ->
                                        let uu____13279 =
                                          let uu___1687_13280 = rc  in
                                          let uu____13281 =
                                            FStar_Util.map_opt
                                              rc.FStar_Syntax_Syntax.residual_typ
                                              (norm cfg env1 [])
                                             in
                                          {
                                            FStar_Syntax_Syntax.residual_effect
                                              =
                                              (uu___1687_13280.FStar_Syntax_Syntax.residual_effect);
                                            FStar_Syntax_Syntax.residual_typ
                                              = uu____13281;
                                            FStar_Syntax_Syntax.residual_flags
                                              =
                                              (uu___1687_13280.FStar_Syntax_Syntax.residual_flags)
                                          }  in
                                        FStar_Pervasives_Native.Some
                                          uu____13279
                                    | uu____13290 -> lopt  in
                                  let def =
                                    FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                     in
                                  let uu___1692_13296 = lb  in
                                  {
                                    FStar_Syntax_Syntax.lbname = lbname;
                                    FStar_Syntax_Syntax.lbunivs =
                                      (uu___1692_13296.FStar_Syntax_Syntax.lbunivs);
                                    FStar_Syntax_Syntax.lbtyp = ty;
                                    FStar_Syntax_Syntax.lbeff =
                                      (uu___1692_13296.FStar_Syntax_Syntax.lbeff);
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs =
                                      (uu___1692_13296.FStar_Syntax_Syntax.lbattrs);
                                    FStar_Syntax_Syntax.lbpos =
                                      (uu___1692_13296.FStar_Syntax_Syntax.lbpos)
                                  }) lbs1
                          in
                       let env' =
                         let uu____13306 =
                           FStar_List.map (fun uu____13322  -> dummy) lbs2
                            in
                         FStar_List.append uu____13306 env  in
                       let body2 = norm cfg env' [] body1  in
                       let uu____13330 =
                         FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                       (match uu____13330 with
                        | (lbs3,body3) ->
                            let t2 =
                              let uu___1701_13346 = t1  in
                              {
                                FStar_Syntax_Syntax.n =
                                  (FStar_Syntax_Syntax.Tm_let
                                     ((true, lbs3), body3));
                                FStar_Syntax_Syntax.pos =
                                  (uu___1701_13346.FStar_Syntax_Syntax.pos);
                                FStar_Syntax_Syntax.vars =
                                  (uu___1701_13346.FStar_Syntax_Syntax.vars)
                              }  in
                            rebuild cfg env stack t2))
              | FStar_Syntax_Syntax.Tm_let (lbs,body) when
                  Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                  ->
                  let uu____13380 = closure_as_term cfg env t1  in
                  rebuild cfg env stack uu____13380
              | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
                  let uu____13401 =
                    FStar_List.fold_right
                      (fun lb  ->
                         fun uu____13479  ->
                           match uu____13479 with
                           | (rec_env,memos,i) ->
                               let bv =
                                 let uu___1717_13604 =
                                   FStar_Util.left
                                     lb.FStar_Syntax_Syntax.lbname
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___1717_13604.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index = i;
                                   FStar_Syntax_Syntax.sort =
                                     (uu___1717_13604.FStar_Syntax_Syntax.sort)
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
                  (match uu____13401 with
                   | (rec_env,memos,uu____13795) ->
                       let uu____13850 =
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
                                let uu____14099 =
                                  let uu____14106 =
                                    let uu____14107 =
                                      let uu____14139 =
                                        FStar_Util.mk_ref
                                          FStar_Pervasives_Native.None
                                         in
                                      (rec_env,
                                        (lb.FStar_Syntax_Syntax.lbdef),
                                        uu____14139, false)
                                       in
                                    Clos uu____14107  in
                                  (FStar_Pervasives_Native.None, uu____14106)
                                   in
                                uu____14099 :: env1)
                           (FStar_Pervasives_Native.snd lbs) env
                          in
                       norm cfg body_env stack body)
              | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____14224  ->
                        let uu____14225 =
                          FStar_Syntax_Print.metadata_to_string m  in
                        FStar_Util.print1 ">> metadata = %s\n" uu____14225);
                   (match m with
                    | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                        reduce_impure_comp cfg env stack head1
                          (FStar_Util.Inl m1) t2
                    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                        reduce_impure_comp cfg env stack head1
                          (FStar_Util.Inr (m1, m')) t2
                    | uu____14249 ->
                        if
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                        then norm cfg env stack head1
                        else
                          (match stack with
                           | uu____14253::uu____14254 ->
                               (match m with
                                | FStar_Syntax_Syntax.Meta_labeled
                                    (l,r,uu____14259) ->
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
                                | uu____14338 -> norm cfg env stack head1)
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
                                     let uu____14386 =
                                       let uu____14407 =
                                         norm_pattern_args cfg env args  in
                                       (names2, uu____14407)  in
                                     FStar_Syntax_Syntax.Meta_pattern
                                       uu____14386
                                 | uu____14436 -> m  in
                               let t2 =
                                 mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                   t1.FStar_Syntax_Syntax.pos
                                  in
                               rebuild cfg env stack t2)))
              | FStar_Syntax_Syntax.Tm_delayed uu____14442 ->
                  let t2 = FStar_Syntax_Subst.compress t1  in
                  norm cfg env stack t2
              | FStar_Syntax_Syntax.Tm_uvar uu____14466 ->
                  let t2 = FStar_Syntax_Subst.compress t1  in
                  (match t2.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_uvar uu____14480 ->
                       if
                         (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                       then
                         let uu____14494 =
                           let uu____14496 =
                             FStar_Range.string_of_range
                               t2.FStar_Syntax_Syntax.pos
                              in
                           let uu____14498 =
                             FStar_Syntax_Print.term_to_string t2  in
                           FStar_Util.format2
                             "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                             uu____14496 uu____14498
                            in
                         failwith uu____14494
                       else
                         (let uu____14503 = inline_closure_env cfg env [] t2
                             in
                          rebuild cfg env stack uu____14503)
                   | uu____14504 -> norm cfg env stack t2)))

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
              let uu____14513 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14513 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14527  ->
                        let uu____14528 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14528);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14541  ->
                        let uu____14542 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14544 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14542 uu____14544);
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
                      | (UnivArgs (us',uu____14557))::stack1 ->
                          ((let uu____14566 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14566
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14574 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14574) us'
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
                      | uu____14610 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14613 ->
                          let uu____14616 =
                            let uu____14618 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14618
                             in
                          failwith uu____14616
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
                  let uu___1829_14646 = cfg  in
                  let uu____14647 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____14647;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1829_14646.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1829_14646.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1829_14646.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1829_14646.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1829_14646.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1829_14646.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1829_14646.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____14678,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14679;
                                    FStar_Syntax_Syntax.vars = uu____14680;_},uu____14681,uu____14682))::uu____14683
                     -> ()
                 | uu____14688 ->
                     let uu____14691 =
                       let uu____14693 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14693
                        in
                     failwith uu____14691);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____14702  ->
                      let uu____14703 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____14705 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____14703
                        uu____14705);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____14709 =
                    let uu____14710 = FStar_Syntax_Subst.compress head3  in
                    uu____14710.FStar_Syntax_Syntax.n  in
                  match uu____14709 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____14731 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____14731
                         in
                      let uu____14732 =
                        let uu____14741 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_bind_repr
                           in
                        FStar_All.pipe_right uu____14741 FStar_Util.must  in
                      (match uu____14732 with
                       | (uu____14756,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14766 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____14777 =
                                    let uu____14778 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14778.FStar_Syntax_Syntax.n  in
                                  match uu____14777 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____14784,uu____14785))
                                      ->
                                      let uu____14794 =
                                        let uu____14795 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____14795.FStar_Syntax_Syntax.n  in
                                      (match uu____14794 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____14801,msrc,uu____14803))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____14812 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____14812
                                       | uu____14813 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____14814 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____14815 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____14815 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___1901_14820 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___1901_14820.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___1901_14820.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___1901_14820.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___1901_14820.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___1901_14820.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____14821 = FStar_List.tl stack
                                        in
                                     let uu____14822 =
                                       let uu____14823 =
                                         let uu____14830 =
                                           let uu____14831 =
                                             let uu____14845 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____14845)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____14831
                                            in
                                         FStar_Syntax_Syntax.mk uu____14830
                                          in
                                       uu____14823
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____14821 uu____14822
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____14861 =
                                       let uu____14863 = is_return body  in
                                       match uu____14863 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____14868;
                                             FStar_Syntax_Syntax.vars =
                                               uu____14869;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____14872 -> false  in
                                     if uu____14861
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
                                          let uu____14896 =
                                            let uu____14903 =
                                              let uu____14904 =
                                                let uu____14923 =
                                                  let uu____14932 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____14932]  in
                                                (uu____14923, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____14904
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____14903
                                             in
                                          uu____14896
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____14971 =
                                            let uu____14972 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____14972.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14971 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____14978::uu____14979::[])
                                              ->
                                              let uu____14984 =
                                                let uu____14991 =
                                                  let uu____14992 =
                                                    let uu____14999 =
                                                      let uu____15000 =
                                                        let uu____15001 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____15001
                                                         in
                                                      let uu____15002 =
                                                        let uu____15005 =
                                                          let uu____15006 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____15006
                                                           in
                                                        [uu____15005]  in
                                                      uu____15000 ::
                                                        uu____15002
                                                       in
                                                    (bind1, uu____14999)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____14992
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____14991
                                                 in
                                              uu____14984
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____15009 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____15024 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____15024
                                          then
                                            let uu____15037 =
                                              let uu____15046 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____15046
                                               in
                                            let uu____15047 =
                                              let uu____15058 =
                                                let uu____15067 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____15067
                                                 in
                                              [uu____15058]  in
                                            uu____15037 :: uu____15047
                                          else []  in
                                        let reified =
                                          let args =
                                            let uu____15116 =
                                              FStar_Syntax_Util.is_layered ed
                                               in
                                            if uu____15116
                                            then
                                              let unit_args =
                                                let uu____15140 =
                                                  let uu____15141 =
                                                    let uu____15144 =
                                                      let uu____15145 =
                                                        FStar_All.pipe_right
                                                          ed
                                                          FStar_Syntax_Util.get_bind_vc_combinator
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____15145
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15144
                                                      FStar_Syntax_Subst.compress
                                                     in
                                                  uu____15141.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____15140 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (uu____15186::uu____15187::bs,uu____15189)
                                                    when
                                                    (FStar_List.length bs) >=
                                                      (Prims.of_int (2))
                                                    ->
                                                    let uu____15241 =
                                                      let uu____15250 =
                                                        FStar_All.pipe_right
                                                          bs
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs)
                                                                -
                                                                (Prims.of_int (2))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____15250
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15241
                                                      (FStar_List.map
                                                         (fun uu____15381  ->
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.unit_const))
                                                | uu____15388 ->
                                                    let uu____15389 =
                                                      let uu____15395 =
                                                        let uu____15397 =
                                                          FStar_Ident.string_of_lid
                                                            ed.FStar_Syntax_Syntax.mname
                                                           in
                                                        let uu____15399 =
                                                          let uu____15401 =
                                                            let uu____15402 =
                                                              FStar_All.pipe_right
                                                                ed
                                                                FStar_Syntax_Util.get_bind_vc_combinator
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____15402
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____15401
                                                            FStar_Syntax_Print.term_to_string
                                                           in
                                                        FStar_Util.format2
                                                          "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                          uu____15397
                                                          uu____15399
                                                         in
                                                      (FStar_Errors.Fatal_UnexpectedEffect,
                                                        uu____15395)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____15389 rng
                                                 in
                                              let uu____15436 =
                                                FStar_Syntax_Syntax.as_arg
                                                  lb.FStar_Syntax_Syntax.lbtyp
                                                 in
                                              let uu____15445 =
                                                let uu____15456 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____15465 =
                                                  let uu____15476 =
                                                    let uu____15487 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head4
                                                       in
                                                    let uu____15496 =
                                                      let uu____15507 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          body2
                                                         in
                                                      [uu____15507]  in
                                                    uu____15487 ::
                                                      uu____15496
                                                     in
                                                  FStar_List.append unit_args
                                                    uu____15476
                                                   in
                                                uu____15456 :: uu____15465
                                                 in
                                              uu____15436 :: uu____15445
                                            else
                                              (let uu____15566 =
                                                 let uu____15577 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____15586 =
                                                   let uu____15597 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   [uu____15597]  in
                                                 uu____15577 :: uu____15586
                                                  in
                                               let uu____15630 =
                                                 let uu____15641 =
                                                   let uu____15652 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       FStar_Syntax_Syntax.tun
                                                      in
                                                   let uu____15661 =
                                                     let uu____15672 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         head4
                                                        in
                                                     let uu____15681 =
                                                       let uu____15692 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let uu____15701 =
                                                         let uu____15712 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2
                                                            in
                                                         [uu____15712]  in
                                                       uu____15692 ::
                                                         uu____15701
                                                        in
                                                     uu____15672 ::
                                                       uu____15681
                                                      in
                                                   uu____15652 :: uu____15661
                                                    in
                                                 FStar_List.append
                                                   maybe_range_arg
                                                   uu____15641
                                                  in
                                               FStar_List.append uu____15566
                                                 uu____15630)
                                             in
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (bind_inst, args))
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____15793  ->
                                             let uu____15794 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____15796 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____15794 uu____15796);
                                        (let uu____15799 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____15799 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____15827 = FStar_Options.defensive ()  in
                        if uu____15827
                        then
                          let is_arg_impure uu____15842 =
                            match uu____15842 with
                            | (e,q) ->
                                let uu____15856 =
                                  let uu____15857 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____15857.FStar_Syntax_Syntax.n  in
                                (match uu____15856 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____15873 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____15873
                                 | uu____15875 -> false)
                             in
                          let uu____15877 =
                            let uu____15879 =
                              let uu____15890 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____15890 :: args  in
                            FStar_Util.for_some is_arg_impure uu____15879  in
                          (if uu____15877
                           then
                             let uu____15916 =
                               let uu____15922 =
                                 let uu____15924 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____15924
                                  in
                               (FStar_Errors.Warning_Defensive, uu____15922)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____15916
                           else ())
                        else ());
                       (let fallback1 uu____15937 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15941  ->
                               let uu____15942 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____15942 "");
                          (let uu____15946 = FStar_List.tl stack  in
                           let uu____15947 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____15946 uu____15947)
                           in
                        let fallback2 uu____15953 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15957  ->
                               let uu____15958 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____15958 "");
                          (let uu____15962 = FStar_List.tl stack  in
                           let uu____15963 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____15962 uu____15963)
                           in
                        let uu____15968 =
                          let uu____15969 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____15969.FStar_Syntax_Syntax.n  in
                        match uu____15968 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____15975 =
                              let uu____15977 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____15977  in
                            if uu____15975
                            then fallback1 ()
                            else
                              (let uu____15982 =
                                 let uu____15984 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____15984  in
                               if uu____15982
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____16001 =
                                      let uu____16006 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____16006 args
                                       in
                                    uu____16001 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____16007 = FStar_List.tl stack  in
                                  norm cfg env uu____16007 t1))
                        | uu____16008 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____16010) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____16034 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____16034  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____16038  ->
                            let uu____16039 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____16039);
                       (let uu____16042 = FStar_List.tl stack  in
                        norm cfg env uu____16042 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____16163  ->
                                match uu____16163 with
                                | (pat,wopt,tm) ->
                                    let uu____16211 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16211)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____16243 = FStar_List.tl stack  in
                      norm cfg env uu____16243 tm
                  | uu____16244 -> fallback ()))

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
              (fun uu____16258  ->
                 let uu____16259 = FStar_Ident.string_of_lid msrc  in
                 let uu____16261 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16263 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16259
                   uu____16261 uu____16263);
            (let uu____16266 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16269 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env)
                     in
                  Prims.op_Negation uu____16269)
                in
             if uu____16266
             then
               let ed =
                 let uu____16274 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16274  in
               let uu____16275 =
                 let uu____16282 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr
                    in
                 FStar_All.pipe_right uu____16282 FStar_Util.must  in
               match uu____16275 with
               | (uu____16319,return_repr) ->
                   let return_inst =
                     let uu____16328 =
                       let uu____16329 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____16329.FStar_Syntax_Syntax.n  in
                     match uu____16328 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16335::[]) ->
                         let uu____16340 =
                           let uu____16347 =
                             let uu____16348 =
                               let uu____16355 =
                                 let uu____16356 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____16356]  in
                               (return_tm, uu____16355)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____16348  in
                           FStar_Syntax_Syntax.mk uu____16347  in
                         uu____16340 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16359 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____16363 =
                     let uu____16370 =
                       let uu____16371 =
                         let uu____16388 =
                           let uu____16399 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____16408 =
                             let uu____16419 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____16419]  in
                           uu____16399 :: uu____16408  in
                         (return_inst, uu____16388)  in
                       FStar_Syntax_Syntax.Tm_app uu____16371  in
                     FStar_Syntax_Syntax.mk uu____16370  in
                   uu____16363 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____16466 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____16466 with
                | FStar_Pervasives_Native.None  ->
                    let uu____16469 =
                      let uu____16471 = FStar_Ident.text_of_lid msrc  in
                      let uu____16473 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____16471 uu____16473
                       in
                    failwith uu____16469
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16476;
                      FStar_TypeChecker_Env.mtarget = uu____16477;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16478;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____16498 =
                      let uu____16500 = FStar_Ident.text_of_lid msrc  in
                      let uu____16502 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____16500 uu____16502
                       in
                    failwith uu____16498
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16505;
                      FStar_TypeChecker_Env.mtarget = uu____16506;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16507;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____16538 =
                        FStar_TypeChecker_Env.is_reifiable_effect env msrc
                         in
                      if uu____16538
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____16543 =
                           let uu____16550 =
                             let uu____16551 =
                               let uu____16570 =
                                 let uu____16579 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____16579]  in
                               (uu____16570, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____16551  in
                           FStar_Syntax_Syntax.mk uu____16550  in
                         uu____16543 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____16612 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    lift uu____16612 t e1))

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
                (fun uu____16682  ->
                   match uu____16682 with
                   | (a,imp) ->
                       let uu____16701 = norm cfg env [] a  in
                       (uu____16701, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____16711  ->
             let uu____16712 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____16714 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____16712 uu____16714);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16740 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16743  -> FStar_Pervasives_Native.Some _16743)
                     uu____16740
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2066_16744 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2066_16744.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2066_16744.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16766 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16769  -> FStar_Pervasives_Native.Some _16769)
                     uu____16766
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2077_16770 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2077_16770.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2077_16770.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____16815  ->
                      match uu____16815 with
                      | (a,i) ->
                          let uu____16835 = norm cfg env [] a  in
                          (uu____16835, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_16857  ->
                       match uu___14_16857 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____16861 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____16861
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2094_16869 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2096_16872 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2096_16872.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2094_16869.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2094_16869.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____16876 = b  in
        match uu____16876 with
        | (x,imp) ->
            let x1 =
              let uu___2104_16884 = x  in
              let uu____16885 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2104_16884.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2104_16884.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16885
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____16896 =
                    let uu____16897 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____16897  in
                  FStar_Pervasives_Native.Some uu____16896
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16908 =
          FStar_List.fold_left
            (fun uu____16942  ->
               fun b  ->
                 match uu____16942 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16908 with | (nbs,uu____17022) -> FStar_List.rev nbs

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
            let uu____17054 =
              let uu___2129_17055 = rc  in
              let uu____17056 =
                if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                then FStar_Pervasives_Native.None
                else
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2129_17055.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17056;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2129_17055.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17054
        | uu____17074 -> lopt

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
            (let uu____17084 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17086 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17084 uu____17086)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_17098  ->
      match uu___15_17098 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17111 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17111 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17115 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____17115)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____17123 = norm_cb cfg  in
            reduce_primops uu____17123 cfg env tm  in
          let uu____17128 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17128
          then tm1
          else
            (let w t =
               let uu___2158_17147 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2158_17147.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2158_17147.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17159 =
                 let uu____17160 = FStar_Syntax_Util.unmeta t  in
                 uu____17160.FStar_Syntax_Syntax.n  in
               match uu____17159 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17172 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17236)::args1,(bv,uu____17239)::bs1) ->
                   let uu____17293 =
                     let uu____17294 = FStar_Syntax_Subst.compress t  in
                     uu____17294.FStar_Syntax_Syntax.n  in
                   (match uu____17293 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17299 -> false)
               | ([],[]) -> true
               | (uu____17330,uu____17331) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17382 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17384 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17382
                    uu____17384)
               else ();
               (let uu____17389 = FStar_Syntax_Util.head_and_args' t  in
                match uu____17389 with
                | (hd1,args) ->
                    let uu____17428 =
                      let uu____17429 = FStar_Syntax_Subst.compress hd1  in
                      uu____17429.FStar_Syntax_Syntax.n  in
                    (match uu____17428 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____17437 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____17439 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____17441 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17437 uu____17439 uu____17441)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17446 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17464 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17466 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17464
                    uu____17466)
               else ();
               (let uu____17471 = FStar_Syntax_Util.is_squash t  in
                match uu____17471 with
                | FStar_Pervasives_Native.Some (uu____17482,t') ->
                    is_applied bs t'
                | uu____17494 ->
                    let uu____17503 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____17503 with
                     | FStar_Pervasives_Native.Some (uu____17514,t') ->
                         is_applied bs t'
                     | uu____17526 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____17550 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17550 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17557)::(q,uu____17559)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17602 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____17604 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17602 uu____17604)
                    else ();
                    (let uu____17609 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____17609 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17614 =
                           let uu____17615 = FStar_Syntax_Subst.compress p
                              in
                           uu____17615.FStar_Syntax_Syntax.n  in
                         (match uu____17614 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____17626 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17626))
                          | uu____17629 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____17632)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____17657 =
                           let uu____17658 = FStar_Syntax_Subst.compress p1
                              in
                           uu____17658.FStar_Syntax_Syntax.n  in
                         (match uu____17657 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____17669 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17669))
                          | uu____17672 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____17676 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____17676 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____17681 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____17681 with
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
                                     let uu____17695 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17695))
                               | uu____17698 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____17703)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____17728 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____17728 with
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
                                     let uu____17742 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17742))
                               | uu____17745 -> FStar_Pervasives_Native.None)
                          | uu____17748 -> FStar_Pervasives_Native.None)
                     | uu____17751 -> FStar_Pervasives_Native.None))
               | uu____17754 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____17767 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17767 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____17773)::[],uu____17774,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17794 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____17796 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____17794
                         uu____17796)
                    else ();
                    is_quantified_const bv phi')
               | uu____17801 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____17816 =
                 let uu____17817 = FStar_Syntax_Subst.compress phi  in
                 uu____17817.FStar_Syntax_Syntax.n  in
               match uu____17816 with
               | FStar_Syntax_Syntax.Tm_match (uu____17823,br::brs) ->
                   let uu____17890 = br  in
                   (match uu____17890 with
                    | (uu____17908,uu____17909,e) ->
                        let r =
                          let uu____17931 = simp_t e  in
                          match uu____17931 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____17943 =
                                FStar_List.for_all
                                  (fun uu____17962  ->
                                     match uu____17962 with
                                     | (uu____17976,uu____17977,e') ->
                                         let uu____17991 = simp_t e'  in
                                         uu____17991 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____17943
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18007 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18017 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18017
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18055 =
                 match uu____18055 with
                 | (t1,q) ->
                     let uu____18076 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18076 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18108 -> (t1, q))
                  in
               let uu____18121 = FStar_Syntax_Util.head_and_args t  in
               match uu____18121 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18201 =
                 let uu____18202 = FStar_Syntax_Util.unmeta ty  in
                 uu____18202.FStar_Syntax_Syntax.n  in
               match uu____18201 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18207) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18212,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18236 -> false  in
             let simplify1 arg =
               let uu____18269 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18269, arg)  in
             let uu____18284 = is_forall_const tm1  in
             match uu____18284 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____18290 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18292 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18290
                       uu____18292)
                  else ();
                  (let uu____18297 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18297))
             | FStar_Pervasives_Native.None  ->
                 let uu____18298 =
                   let uu____18299 = FStar_Syntax_Subst.compress tm1  in
                   uu____18299.FStar_Syntax_Syntax.n  in
                 (match uu____18298 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18303;
                              FStar_Syntax_Syntax.vars = uu____18304;_},uu____18305);
                         FStar_Syntax_Syntax.pos = uu____18306;
                         FStar_Syntax_Syntax.vars = uu____18307;_},args)
                      ->
                      let uu____18337 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18337
                      then
                        let uu____18340 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18340 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18398)::
                             (uu____18399,(arg,uu____18401))::[] ->
                             maybe_auto_squash arg
                         | (uu____18474,(arg,uu____18476))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18477)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18550)::uu____18551::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18621::(FStar_Pervasives_Native.Some (false
                                         ),uu____18622)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18692 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18710 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18710
                         then
                           let uu____18713 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18713 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18771)::uu____18772::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18842::(FStar_Pervasives_Native.Some (true
                                           ),uu____18843)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18913)::(uu____18914,(arg,uu____18916))::[]
                               -> maybe_auto_squash arg
                           | (uu____18989,(arg,uu____18991))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18992)::[]
                               -> maybe_auto_squash arg
                           | uu____19065 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19083 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19083
                            then
                              let uu____19086 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19086 with
                              | uu____19144::(FStar_Pervasives_Native.Some
                                              (true ),uu____19145)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19215)::uu____19216::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19286)::(uu____19287,(arg,uu____19289))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19362,(p,uu____19364))::(uu____19365,
                                                                (q,uu____19367))::[]
                                  ->
                                  let uu____19439 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19439
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19444 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19462 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19462
                               then
                                 let uu____19465 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19465 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19523)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19524)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19598)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19599)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19673)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19674)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19748)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19749)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19823,(arg,uu____19825))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19826)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19899)::(uu____19900,(arg,uu____19902))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19975,(arg,uu____19977))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19978)::[]
                                     ->
                                     let uu____20051 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20051
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20052)::(uu____20053,(arg,uu____20055))::[]
                                     ->
                                     let uu____20128 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20128
                                 | (uu____20129,(p,uu____20131))::(uu____20132,
                                                                   (q,uu____20134))::[]
                                     ->
                                     let uu____20206 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20206
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20211 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20229 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20229
                                  then
                                    let uu____20232 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20232 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20290)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20334)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20378 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20396 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20396
                                     then
                                       match args with
                                       | (t,uu____20400)::[] ->
                                           let uu____20425 =
                                             let uu____20426 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20426.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20425 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20429::[],body,uu____20431)
                                                ->
                                                let uu____20466 = simp_t body
                                                   in
                                                (match uu____20466 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20472 -> tm1)
                                            | uu____20476 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20478))::(t,uu____20480)::[]
                                           ->
                                           let uu____20520 =
                                             let uu____20521 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20521.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20520 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20524::[],body,uu____20526)
                                                ->
                                                let uu____20561 = simp_t body
                                                   in
                                                (match uu____20561 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20569 -> tm1)
                                            | uu____20573 -> tm1)
                                       | uu____20574 -> tm1
                                     else
                                       (let uu____20587 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20587
                                        then
                                          match args with
                                          | (t,uu____20591)::[] ->
                                              let uu____20616 =
                                                let uu____20617 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20617.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20616 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20620::[],body,uu____20622)
                                                   ->
                                                   let uu____20657 =
                                                     simp_t body  in
                                                   (match uu____20657 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20663 -> tm1)
                                               | uu____20667 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20669))::(t,uu____20671)::[]
                                              ->
                                              let uu____20711 =
                                                let uu____20712 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20712.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20711 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20715::[],body,uu____20717)
                                                   ->
                                                   let uu____20752 =
                                                     simp_t body  in
                                                   (match uu____20752 with
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
                                                    | uu____20760 -> tm1)
                                               | uu____20764 -> tm1)
                                          | uu____20765 -> tm1
                                        else
                                          (let uu____20778 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20778
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20781;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20782;_},uu____20783)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20809;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20810;_},uu____20811)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20837 -> tm1
                                           else
                                             (let uu____20850 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____20850
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____20864 =
                                                    let uu____20865 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____20865.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____20864 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____20876 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____20890 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____20890
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____20929 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____20929
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____20935 =
                                                         let uu____20936 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____20936.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____20935 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____20939 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____20947 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____20947
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____20956
                                                                  =
                                                                  let uu____20957
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____20957.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____20956
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____20963)
                                                                    -> hd1
                                                                | uu____20988
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____20992
                                                                =
                                                                let uu____21003
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____21003]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____20992)
                                                       | uu____21036 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21041 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____21041 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21061 ->
                                                     let uu____21070 =
                                                       let uu____21077 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____21077 cfg env
                                                        in
                                                     uu____21070 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21083;
                         FStar_Syntax_Syntax.vars = uu____21084;_},args)
                      ->
                      let uu____21110 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21110
                      then
                        let uu____21113 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21113 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21171)::
                             (uu____21172,(arg,uu____21174))::[] ->
                             maybe_auto_squash arg
                         | (uu____21247,(arg,uu____21249))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21250)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21323)::uu____21324::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21394::(FStar_Pervasives_Native.Some (false
                                         ),uu____21395)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21465 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21483 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21483
                         then
                           let uu____21486 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21486 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21544)::uu____21545::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21615::(FStar_Pervasives_Native.Some (true
                                           ),uu____21616)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21686)::(uu____21687,(arg,uu____21689))::[]
                               -> maybe_auto_squash arg
                           | (uu____21762,(arg,uu____21764))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21765)::[]
                               -> maybe_auto_squash arg
                           | uu____21838 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21856 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21856
                            then
                              let uu____21859 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21859 with
                              | uu____21917::(FStar_Pervasives_Native.Some
                                              (true ),uu____21918)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21988)::uu____21989::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22059)::(uu____22060,(arg,uu____22062))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22135,(p,uu____22137))::(uu____22138,
                                                                (q,uu____22140))::[]
                                  ->
                                  let uu____22212 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22212
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22217 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22235 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22235
                               then
                                 let uu____22238 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____22238 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22296)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22297)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22371)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22372)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22446)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22447)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22521)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22522)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22596,(arg,uu____22598))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22599)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22672)::(uu____22673,(arg,uu____22675))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____22748,(arg,uu____22750))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____22751)::[]
                                     ->
                                     let uu____22824 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22824
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22825)::(uu____22826,(arg,uu____22828))::[]
                                     ->
                                     let uu____22901 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22901
                                 | (uu____22902,(p,uu____22904))::(uu____22905,
                                                                   (q,uu____22907))::[]
                                     ->
                                     let uu____22979 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22979
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22984 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23002 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23002
                                  then
                                    let uu____23005 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23005 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23063)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23107)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23151 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23169 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23169
                                     then
                                       match args with
                                       | (t,uu____23173)::[] ->
                                           let uu____23198 =
                                             let uu____23199 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23199.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23198 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23202::[],body,uu____23204)
                                                ->
                                                let uu____23239 = simp_t body
                                                   in
                                                (match uu____23239 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23245 -> tm1)
                                            | uu____23249 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23251))::(t,uu____23253)::[]
                                           ->
                                           let uu____23293 =
                                             let uu____23294 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23294.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23293 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23297::[],body,uu____23299)
                                                ->
                                                let uu____23334 = simp_t body
                                                   in
                                                (match uu____23334 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____23342 -> tm1)
                                            | uu____23346 -> tm1)
                                       | uu____23347 -> tm1
                                     else
                                       (let uu____23360 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____23360
                                        then
                                          match args with
                                          | (t,uu____23364)::[] ->
                                              let uu____23389 =
                                                let uu____23390 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23390.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23389 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23393::[],body,uu____23395)
                                                   ->
                                                   let uu____23430 =
                                                     simp_t body  in
                                                   (match uu____23430 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____23436 -> tm1)
                                               | uu____23440 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____23442))::(t,uu____23444)::[]
                                              ->
                                              let uu____23484 =
                                                let uu____23485 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23485.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23484 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23488::[],body,uu____23490)
                                                   ->
                                                   let uu____23525 =
                                                     simp_t body  in
                                                   (match uu____23525 with
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
                                                    | uu____23533 -> tm1)
                                               | uu____23537 -> tm1)
                                          | uu____23538 -> tm1
                                        else
                                          (let uu____23551 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____23551
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23554;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23555;_},uu____23556)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23582;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23583;_},uu____23584)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____23610 -> tm1
                                           else
                                             (let uu____23623 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____23623
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____23637 =
                                                    let uu____23638 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____23638.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____23637 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____23649 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____23663 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____23663
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____23698 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____23698
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____23704 =
                                                         let uu____23705 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____23705.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____23704 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____23708 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____23716 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____23716
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____23725
                                                                  =
                                                                  let uu____23726
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____23726.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____23725
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____23732)
                                                                    -> hd1
                                                                | uu____23757
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____23761
                                                                =
                                                                let uu____23772
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____23772]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____23761)
                                                       | uu____23805 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____23810 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____23810 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____23830 ->
                                                     let uu____23839 =
                                                       let uu____23846 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____23846 cfg env
                                                        in
                                                     uu____23839 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____23857 = simp_t t  in
                      (match uu____23857 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____23866 ->
                      let uu____23889 = is_const_match tm1  in
                      (match uu____23889 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____23898 -> tm1))

and (is_wp_req_ens_commutation :
  FStar_TypeChecker_Cfg.cfg ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun cfg  ->
    fun env  ->
      fun t  ->
        let is_fv t1 lid =
          let uu____23916 =
            let uu____23917 = FStar_Syntax_Subst.compress t1  in
            uu____23917.FStar_Syntax_Syntax.n  in
          match uu____23916 with
          | FStar_Syntax_Syntax.Tm_uinst (t2,uu____23922) ->
              let uu____23927 =
                let uu____23928 = FStar_Syntax_Subst.compress t2  in
                uu____23928.FStar_Syntax_Syntax.n  in
              (match uu____23927 with
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   FStar_Syntax_Syntax.fv_eq_lid fv lid
               | uu____23933 -> false)
          | FStar_Syntax_Syntax.Tm_fvar fv ->
              FStar_Syntax_Syntax.fv_eq_lid fv lid
          | uu____23936 -> false  in
        let us_of t1 =
          let uu____23944 =
            let uu____23945 = FStar_Syntax_Subst.compress t1  in
            uu____23945.FStar_Syntax_Syntax.n  in
          match uu____23944 with
          | FStar_Syntax_Syntax.Tm_uinst (uu____23948,us) -> us
          | FStar_Syntax_Syntax.Tm_fvar uu____23954 -> []
          | uu____23955 ->
              failwith "Impossible! us_of called with a non Tm_uinst term"
           in
        let mk_app1 lid us args r =
          let uu____23978 =
            let uu____23979 =
              let uu____23980 =
                FStar_Syntax_Syntax.lid_as_fv lid
                  (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____23980 FStar_Syntax_Syntax.fv_to_tm
               in
            FStar_All.pipe_right uu____23979
              (fun t1  -> FStar_Syntax_Syntax.mk_Tm_uinst t1 us)
             in
          FStar_All.pipe_right uu____23978
            (fun f  ->
               FStar_Syntax_Syntax.mk_Tm_app f args
                 FStar_Pervasives_Native.None r)
           in
        let reduce_as_requires args r =
          if (FStar_List.length args) <> (Prims.of_int (2))
          then FStar_Pervasives_Native.None
          else
            (let uu____24016 = args  in
             match uu____24016 with
             | uu____24019::(wp,uu____24021)::[] ->
                 let wp1 =
                   let uu____24063 =
                     FStar_TypeChecker_Cfg.config' []
                       [FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF;
                       FStar_TypeChecker_Env.Beta]
                       cfg.FStar_TypeChecker_Cfg.tcenv
                      in
                   norm uu____24063 env [] wp  in
                 let uu____24064 =
                   let uu____24065 = FStar_Syntax_Subst.compress wp1  in
                   uu____24065.FStar_Syntax_Syntax.n  in
                 (match uu____24064 with
                  | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                      is_fv head1 FStar_Parser_Const.as_wp ->
                      let uu____24096 = args1  in
                      (match uu____24096 with
                       | uu____24109::(req,uu____24111)::uu____24112::[] ->
                           FStar_Pervasives_Native.Some req)
                  | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                      is_fv head1 FStar_Parser_Const.pure_return_lid ->
                      let uu____24195 =
                        let uu____24196 = us_of head1  in
                        mk_app1 FStar_Parser_Const.as_req_return uu____24196
                          args1 r
                         in
                      FStar_All.pipe_left
                        (fun _24199  -> FStar_Pervasives_Native.Some _24199)
                        uu____24195
                  | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                      is_fv head1 FStar_Parser_Const.pure_bind_lid ->
                      let uu____24226 =
                        let uu____24227 = us_of head1  in
                        let uu____24228 =
                          FStar_All.pipe_right args1 FStar_List.tl  in
                        mk_app1 FStar_Parser_Const.as_req_bind uu____24227
                          uu____24228 r
                         in
                      FStar_All.pipe_left
                        (fun _24249  -> FStar_Pervasives_Native.Some _24249)
                        uu____24226
                  | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                      is_fv head1 FStar_Parser_Const.pure_assume_wp_lid ->
                      let uu____24276 =
                        let uu____24277 = us_of head1  in
                        mk_app1 FStar_Parser_Const.as_req_assume uu____24277
                          args1 r
                         in
                      FStar_All.pipe_left
                        (fun _24280  -> FStar_Pervasives_Native.Some _24280)
                        uu____24276
                  | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                      is_fv head1 FStar_Parser_Const.pure_assert_wp_lid ->
                      let uu____24307 =
                        let uu____24308 = us_of head1  in
                        mk_app1 FStar_Parser_Const.as_req_assert uu____24308
                          args1 r
                         in
                      FStar_All.pipe_left
                        (fun _24311  -> FStar_Pervasives_Native.Some _24311)
                        uu____24307
                  | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                      is_fv head1 FStar_Parser_Const.pure_if_then_else_lid ->
                      let uu____24338 =
                        let uu____24339 = us_of head1  in
                        mk_app1 FStar_Parser_Const.as_req_if_then_else
                          uu____24339 args1 r
                         in
                      FStar_All.pipe_left
                        (fun _24342  -> FStar_Pervasives_Native.Some _24342)
                        uu____24338
                  | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                      is_fv head1 FStar_Parser_Const.pure_ite_lid ->
                      let uu____24369 =
                        let uu____24370 = us_of head1  in
                        mk_app1 FStar_Parser_Const.as_req_ite uu____24370
                          args1 r
                         in
                      FStar_All.pipe_left
                        (fun _24373  -> FStar_Pervasives_Native.Some _24373)
                        uu____24369
                  | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                      is_fv head1 FStar_Parser_Const.pure_close_lid ->
                      let uu____24400 =
                        let uu____24401 = us_of head1  in
                        mk_app1 FStar_Parser_Const.as_req_close uu____24401
                          args1 r
                         in
                      FStar_All.pipe_left
                        (fun _24404  -> FStar_Pervasives_Native.Some _24404)
                        uu____24400
                  | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                      is_fv head1 FStar_Parser_Const.pure_null_lid ->
                      let uu____24431 =
                        let uu____24432 = us_of head1  in
                        mk_app1 FStar_Parser_Const.as_req_null uu____24432
                          args1 r
                         in
                      FStar_All.pipe_left
                        (fun _24435  -> FStar_Pervasives_Native.Some _24435)
                        uu____24431
                  | uu____24436 -> FStar_Pervasives_Native.None))
           in
        let reduce_as_ensures args r =
          if
            ((FStar_List.length args) <> (Prims.of_int (2))) &&
              ((FStar_List.length args) <> (Prims.of_int (3)))
          then FStar_Pervasives_Native.None
          else
            (let uu____24475 =
               if (FStar_List.length args) = (Prims.of_int (2))
               then
                 let uu____24515 = args  in
                 match uu____24515 with
                 | uu____24530::(wp,uu____24532)::[] ->
                     (wp, FStar_Pervasives_Native.None)
               else
                 (let uu____24593 = args  in
                  match uu____24593 with
                  | uu____24608::(wp,uu____24610)::arg::[] ->
                      (wp, (FStar_Pervasives_Native.Some arg)))
                in
             match uu____24475 with
             | (wp,remaining_arg) ->
                 let wp1 =
                   let uu____24711 =
                     FStar_TypeChecker_Cfg.config' []
                       [FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF;
                       FStar_TypeChecker_Env.Beta]
                       cfg.FStar_TypeChecker_Cfg.tcenv
                      in
                   norm uu____24711 env [] wp  in
                 let ens_opt =
                   let uu____24715 =
                     let uu____24716 = FStar_Syntax_Subst.compress wp1  in
                     uu____24716.FStar_Syntax_Syntax.n  in
                   match uu____24715 with
                   | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                       is_fv head1 FStar_Parser_Const.as_wp ->
                       let uu____24747 = args1  in
                       (match uu____24747 with
                        | uu____24760::uu____24761::(ens,uu____24763)::[] ->
                            FStar_Pervasives_Native.Some ens)
                   | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                       is_fv head1 FStar_Parser_Const.pure_return_lid ->
                       let uu____24846 =
                         let uu____24847 = us_of head1  in
                         mk_app1 FStar_Parser_Const.as_ens_return uu____24847
                           args1 r
                          in
                       FStar_All.pipe_left
                         (fun _24850  -> FStar_Pervasives_Native.Some _24850)
                         uu____24846
                   | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                       is_fv head1 FStar_Parser_Const.pure_bind_lid ->
                       let uu____24877 =
                         let uu____24878 = us_of head1  in
                         let uu____24879 =
                           FStar_All.pipe_right args1 FStar_List.tl  in
                         mk_app1 FStar_Parser_Const.as_ens_bind uu____24878
                           uu____24879 r
                          in
                       FStar_All.pipe_left
                         (fun _24900  -> FStar_Pervasives_Native.Some _24900)
                         uu____24877
                   | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                       is_fv head1 FStar_Parser_Const.pure_assume_wp_lid ->
                       let uu____24927 =
                         let uu____24928 = us_of head1  in
                         mk_app1 FStar_Parser_Const.as_ens_assume uu____24928
                           args1 r
                          in
                       FStar_All.pipe_left
                         (fun _24931  -> FStar_Pervasives_Native.Some _24931)
                         uu____24927
                   | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                       is_fv head1 FStar_Parser_Const.pure_assert_wp_lid ->
                       let uu____24958 =
                         let uu____24959 = us_of head1  in
                         mk_app1 FStar_Parser_Const.as_ens_assert uu____24959
                           args1 r
                          in
                       FStar_All.pipe_left
                         (fun _24962  -> FStar_Pervasives_Native.Some _24962)
                         uu____24958
                   | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                       is_fv head1 FStar_Parser_Const.pure_if_then_else_lid
                       ->
                       let uu____24989 =
                         let uu____24990 = us_of head1  in
                         mk_app1 FStar_Parser_Const.as_ens_if_then_else
                           uu____24990 args1 r
                          in
                       FStar_All.pipe_left
                         (fun _24993  -> FStar_Pervasives_Native.Some _24993)
                         uu____24989
                   | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                       is_fv head1 FStar_Parser_Const.pure_ite_lid ->
                       let uu____25020 =
                         let uu____25021 = us_of head1  in
                         mk_app1 FStar_Parser_Const.as_ens_ite uu____25021
                           args1 r
                          in
                       FStar_All.pipe_left
                         (fun _25024  -> FStar_Pervasives_Native.Some _25024)
                         uu____25020
                   | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                       is_fv head1 FStar_Parser_Const.pure_close_lid ->
                       let uu____25051 =
                         let uu____25052 = us_of head1  in
                         mk_app1 FStar_Parser_Const.as_ens_close uu____25052
                           args1 r
                          in
                       FStar_All.pipe_left
                         (fun _25055  -> FStar_Pervasives_Native.Some _25055)
                         uu____25051
                   | FStar_Syntax_Syntax.Tm_app (head1,args1) when
                       is_fv head1 FStar_Parser_Const.pure_null_lid ->
                       let uu____25082 =
                         let uu____25083 = us_of head1  in
                         mk_app1 FStar_Parser_Const.as_ens_null uu____25083
                           args1 r
                          in
                       FStar_All.pipe_left
                         (fun _25086  -> FStar_Pervasives_Native.Some _25086)
                         uu____25082
                   | uu____25087 -> FStar_Pervasives_Native.None  in
                 (match (ens_opt, remaining_arg) with
                  | (FStar_Pervasives_Native.Some
                     ens,FStar_Pervasives_Native.None ) ->
                      FStar_Pervasives_Native.Some ens
                  | (FStar_Pervasives_Native.Some
                     ens,FStar_Pervasives_Native.Some arg) ->
                      let uu____25153 =
                        FStar_Syntax_Syntax.mk_Tm_app ens [arg]
                          FStar_Pervasives_Native.None FStar_Range.dummyRange
                         in
                      FStar_All.pipe_left
                        (fun _25172  -> FStar_Pervasives_Native.Some _25172)
                        uu____25153
                  | (uu____25173,uu____25174) -> FStar_Pervasives_Native.None))
           in
        let cfg_restricted uu____25204 =
          FStar_TypeChecker_Cfg.config' []
            [FStar_TypeChecker_Env.UnfoldAttr
               [FStar_Parser_Const.wp_req_ens_attr]]
            cfg.FStar_TypeChecker_Cfg.tcenv
           in
        let topt =
          let uu____25208 =
            let uu____25209 = FStar_Syntax_Subst.compress t  in
            uu____25209.FStar_Syntax_Syntax.n  in
          match uu____25208 with
          | FStar_Syntax_Syntax.Tm_app (head1,args) when
              is_fv head1 FStar_Parser_Const.as_requires_opaque ->
              reduce_as_requires args t.FStar_Syntax_Syntax.pos
          | FStar_Syntax_Syntax.Tm_app (head1,args) when
              is_fv head1 FStar_Parser_Const.as_ensures_opaque ->
              reduce_as_ensures args t.FStar_Syntax_Syntax.pos
          | uu____25266 -> FStar_Pervasives_Native.None  in
        let uu____25267 =
          let uu____25272 = cfg_restricted ()  in norm uu____25272 env []  in
        FStar_Util.map_option uu____25267 topt

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____25282  ->
               (let uu____25284 = FStar_Syntax_Print.tag_of_term t  in
                let uu____25286 = FStar_Syntax_Print.term_to_string t  in
                let uu____25288 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____25296 =
                  let uu____25298 =
                    let uu____25301 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____25301
                     in
                  stack_to_string uu____25298  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____25284 uu____25286 uu____25288 uu____25296);
               (let uu____25326 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____25326
                then
                  let uu____25330 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____25330 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____25337 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____25339 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____25341 =
                          let uu____25343 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____25343
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____25337
                          uu____25339 uu____25341);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____25365 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____25373)::uu____25374 -> true
                | uu____25384 -> false)
              in
           if uu____25365
           then
             let uu____25387 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____25387 (norm cfg env stack)
           else
             (let t_opt = is_wp_req_ens_commutation cfg env t  in
              let uu____25395 = FStar_All.pipe_right t_opt FStar_Util.is_some
                 in
              if uu____25395
              then
                ((let uu____25402 =
                    FStar_All.pipe_left
                      (FStar_TypeChecker_Env.debug
                         cfg.FStar_TypeChecker_Cfg.tcenv)
                      (FStar_Options.Other "WPReqEns")
                     in
                  if uu____25402
                  then
                    let uu____25407 = FStar_Syntax_Print.term_to_string t  in
                    let uu____25409 =
                      let uu____25411 =
                        FStar_All.pipe_right t_opt FStar_Util.must  in
                      FStar_All.pipe_right uu____25411
                        FStar_Syntax_Print.term_to_string
                       in
                    FStar_Util.print2
                      "In rebuild: reduced a wp req ens commutation from \n%s\n to \n%s"
                      uu____25407 uu____25409
                  else ());
                 (let uu____25418 =
                    FStar_All.pipe_right t_opt FStar_Util.must  in
                  FStar_All.pipe_right uu____25418 (norm cfg env stack)))
              else
                (let t1 = maybe_simplify cfg env stack t  in
                 match stack with
                 | [] -> t1
                 | (Debug (tm,time_then))::stack1 ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let time_now = FStar_Util.now ()  in
                         let uu____25432 =
                           let uu____25434 =
                             let uu____25436 =
                               FStar_Util.time_diff time_then time_now  in
                             FStar_Pervasives_Native.snd uu____25436  in
                           FStar_Util.string_of_int uu____25434  in
                         let uu____25443 =
                           FStar_Syntax_Print.term_to_string tm  in
                         let uu____25445 =
                           FStar_TypeChecker_Cfg.cfg_to_string cfg  in
                         let uu____25447 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print4
                           "Normalizer result timing (%s ms){\nOn term {\n%s\n}\nwith steps {%s}\nresult is{\n\n%s\n}\n}\n"
                           uu____25432 uu____25443 uu____25445 uu____25447)
                      else ();
                      rebuild cfg env stack1 t1)
                 | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
                 | (Meta (uu____25456,m,r))::stack1 ->
                     let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                     rebuild cfg env stack1 t2
                 | (MemoLazy r)::stack1 ->
                     (set_memo cfg r (env, t1);
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____25485  ->
                           let uu____25486 =
                             FStar_Syntax_Print.term_to_string t1  in
                           FStar_Util.print1 "\tSet memo %s\n" uu____25486);
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
                     let uu____25529 =
                       let uu___2964_25530 =
                         FStar_Syntax_Util.abs bs1 t1 lopt1  in
                       {
                         FStar_Syntax_Syntax.n =
                           (uu___2964_25530.FStar_Syntax_Syntax.n);
                         FStar_Syntax_Syntax.pos = r;
                         FStar_Syntax_Syntax.vars =
                           (uu___2964_25530.FStar_Syntax_Syntax.vars)
                       }  in
                     rebuild cfg env stack1 uu____25529
                 | (Arg
                     (Univ uu____25533,uu____25534,uu____25535))::uu____25536
                     -> failwith "Impossible"
                 | (Arg (Dummy ,uu____25540,uu____25541))::uu____25542 ->
                     failwith "Impossible"
                 | (UnivArgs (us,r))::stack1 ->
                     let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                     rebuild cfg env stack1 t2
                 | (Arg
                     (Clos (env_arg,tm,uu____25558,uu____25559),aq,r))::stack1
                     when
                     let uu____25611 = head_of t1  in
                     FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____25611
                     ->
                     let t2 =
                       let uu____25615 =
                         let uu____25620 =
                           let uu____25621 = closure_as_term cfg env_arg tm
                              in
                           (uu____25621, aq)  in
                         FStar_Syntax_Syntax.extend_app t1 uu____25620  in
                       uu____25615 FStar_Pervasives_Native.None r  in
                     rebuild cfg env stack1 t2
                 | (Arg (Clos (env_arg,tm,m,uu____25631),aq,r))::stack1 ->
                     (FStar_TypeChecker_Cfg.log cfg
                        (fun uu____25686  ->
                           let uu____25687 =
                             FStar_Syntax_Print.term_to_string tm  in
                           FStar_Util.print1 "Rebuilding with arg %s\n"
                             uu____25687);
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
                        (let uu____25707 = FStar_ST.op_Bang m  in
                         match uu____25707 with
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
                         | FStar_Pervasives_Native.Some (uu____25795,a) ->
                             let t2 =
                               FStar_Syntax_Syntax.extend_app t1 (a, aq)
                                 FStar_Pervasives_Native.None r
                                in
                             rebuild cfg env_arg stack1 t2))
                 | (App (env1,head1,aq,r))::stack' when
                     should_reify cfg stack ->
                     let t0 = t1  in
                     let fallback msg uu____25851 =
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____25856  ->
                            let uu____25857 =
                              FStar_Syntax_Print.term_to_string t1  in
                            FStar_Util.print2 "Not reifying%s: %s\n" msg
                              uu____25857);
                       (let t2 =
                          FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                            FStar_Pervasives_Native.None r
                           in
                        rebuild cfg env1 stack' t2)
                        in
                     let uu____25867 =
                       let uu____25868 = FStar_Syntax_Subst.compress t1  in
                       uu____25868.FStar_Syntax_Syntax.n  in
                     (match uu____25867 with
                      | FStar_Syntax_Syntax.Tm_meta
                          (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                          do_reify_monadic (fallback " (1)") cfg env1 stack
                            t2 m ty
                      | FStar_Syntax_Syntax.Tm_meta
                          (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                           (msrc,mtgt,ty))
                          ->
                          let lifted =
                            let uu____25896 = closure_as_term cfg env1 ty  in
                            reify_lift cfg t2 msrc mtgt uu____25896  in
                          (FStar_TypeChecker_Cfg.log cfg
                             (fun uu____25900  ->
                                let uu____25901 =
                                  FStar_Syntax_Print.term_to_string lifted
                                   in
                                FStar_Util.print1 "Reified lift to (1): %s\n"
                                  uu____25901);
                           (let uu____25904 = FStar_List.tl stack  in
                            norm cfg env1 uu____25904 lifted))
                      | FStar_Syntax_Syntax.Tm_app
                          ({
                             FStar_Syntax_Syntax.n =
                               FStar_Syntax_Syntax.Tm_constant
                               (FStar_Const.Const_reflect uu____25905);
                             FStar_Syntax_Syntax.pos = uu____25906;
                             FStar_Syntax_Syntax.vars = uu____25907;_},
                           (e,uu____25909)::[])
                          -> norm cfg env1 stack' e
                      | FStar_Syntax_Syntax.Tm_app uu____25948 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                          ->
                          let uu____25965 =
                            FStar_Syntax_Util.head_and_args t1  in
                          (match uu____25965 with
                           | (hd1,args) ->
                               let uu____26008 =
                                 let uu____26009 =
                                   FStar_Syntax_Util.un_uinst hd1  in
                                 uu____26009.FStar_Syntax_Syntax.n  in
                               (match uu____26008 with
                                | FStar_Syntax_Syntax.Tm_fvar fv ->
                                    let uu____26013 =
                                      FStar_TypeChecker_Cfg.find_prim_step
                                        cfg fv
                                       in
                                    (match uu____26013 with
                                     | FStar_Pervasives_Native.Some
                                         {
                                           FStar_TypeChecker_Cfg.name =
                                             uu____26016;
                                           FStar_TypeChecker_Cfg.arity =
                                             uu____26017;
                                           FStar_TypeChecker_Cfg.univ_arity =
                                             uu____26018;
                                           FStar_TypeChecker_Cfg.auto_reflect
                                             = FStar_Pervasives_Native.Some
                                             n1;
                                           FStar_TypeChecker_Cfg.strong_reduction_ok
                                             = uu____26020;
                                           FStar_TypeChecker_Cfg.requires_binder_substitution
                                             = uu____26021;
                                           FStar_TypeChecker_Cfg.interpretation
                                             = uu____26022;
                                           FStar_TypeChecker_Cfg.interpretation_nbe
                                             = uu____26023;_}
                                         when (FStar_List.length args) = n1
                                         -> norm cfg env1 stack' t1
                                     | uu____26059 -> fallback " (3)" ())
                                | uu____26063 -> fallback " (4)" ()))
                      | uu____26065 -> fallback " (2)" ())
                 | (App (env1,head1,aq,r))::stack1 ->
                     let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack1 t2
                 | (Match (env',branches,cfg1,r))::stack1 ->
                     (FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____26091  ->
                           let uu____26092 =
                             FStar_Syntax_Print.term_to_string t1  in
                           FStar_Util.print1
                             "Rebuilding with match, scrutinee is %s ...\n"
                             uu____26092);
                      (let scrutinee_env = env  in
                       let env1 = env'  in
                       let scrutinee = t1  in
                       let norm_and_rebuild_match uu____26103 =
                         FStar_TypeChecker_Cfg.log cfg1
                           (fun uu____26108  ->
                              let uu____26109 =
                                FStar_Syntax_Print.term_to_string scrutinee
                                 in
                              let uu____26111 =
                                let uu____26113 =
                                  FStar_All.pipe_right branches
                                    (FStar_List.map
                                       (fun uu____26143  ->
                                          match uu____26143 with
                                          | (p,uu____26154,uu____26155) ->
                                              FStar_Syntax_Print.pat_to_string
                                                p))
                                   in
                                FStar_All.pipe_right uu____26113
                                  (FStar_String.concat "\n\t")
                                 in
                              FStar_Util.print2
                                "match is irreducible: scrutinee=%s\nbranches=%s\n"
                                uu____26109 uu____26111);
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
                                   (fun uu___16_26177  ->
                                      match uu___16_26177 with
                                      | FStar_TypeChecker_Env.InliningDelta 
                                          -> true
                                      | FStar_TypeChecker_Env.Eager_unfolding_only
                                           -> true
                                      | uu____26181 -> false))
                               in
                            let steps =
                              let uu___3132_26184 =
                                cfg1.FStar_TypeChecker_Cfg.steps  in
                              {
                                FStar_TypeChecker_Cfg.beta =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.beta);
                                FStar_TypeChecker_Cfg.iota =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.iota);
                                FStar_TypeChecker_Cfg.zeta = false;
                                FStar_TypeChecker_Cfg.weak =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.weak);
                                FStar_TypeChecker_Cfg.hnf =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.hnf);
                                FStar_TypeChecker_Cfg.primops =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.primops);
                                FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                  =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                FStar_TypeChecker_Cfg.unfold_until =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_only =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_fully =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.unfold_fully);
                                FStar_TypeChecker_Cfg.unfold_attr =
                                  FStar_Pervasives_Native.None;
                                FStar_TypeChecker_Cfg.unfold_tac = false;
                                FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                  =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                FStar_TypeChecker_Cfg.simplify =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.simplify);
                                FStar_TypeChecker_Cfg.erase_universes =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.erase_universes);
                                FStar_TypeChecker_Cfg.allow_unbound_universes
                                  =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                FStar_TypeChecker_Cfg.reify_ =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.reify_);
                                FStar_TypeChecker_Cfg.compress_uvars =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.compress_uvars);
                                FStar_TypeChecker_Cfg.no_full_norm =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.no_full_norm);
                                FStar_TypeChecker_Cfg.check_no_uvars =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.check_no_uvars);
                                FStar_TypeChecker_Cfg.unmeta =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.unmeta);
                                FStar_TypeChecker_Cfg.unascribe =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.unascribe);
                                FStar_TypeChecker_Cfg.in_full_norm_request =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.in_full_norm_request);
                                FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                  =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                                FStar_TypeChecker_Cfg.nbe_step =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.nbe_step);
                                FStar_TypeChecker_Cfg.for_extraction =
                                  (uu___3132_26184.FStar_TypeChecker_Cfg.for_extraction)
                              }  in
                            let uu___3135_26191 = cfg1  in
                            {
                              FStar_TypeChecker_Cfg.steps = steps;
                              FStar_TypeChecker_Cfg.tcenv =
                                (uu___3135_26191.FStar_TypeChecker_Cfg.tcenv);
                              FStar_TypeChecker_Cfg.debug =
                                (uu___3135_26191.FStar_TypeChecker_Cfg.debug);
                              FStar_TypeChecker_Cfg.delta_level = new_delta;
                              FStar_TypeChecker_Cfg.primitive_steps =
                                (uu___3135_26191.FStar_TypeChecker_Cfg.primitive_steps);
                              FStar_TypeChecker_Cfg.strong = true;
                              FStar_TypeChecker_Cfg.memoize_lazy =
                                (uu___3135_26191.FStar_TypeChecker_Cfg.memoize_lazy);
                              FStar_TypeChecker_Cfg.normalize_pure_lets =
                                (uu___3135_26191.FStar_TypeChecker_Cfg.normalize_pure_lets);
                              FStar_TypeChecker_Cfg.reifying =
                                (uu___3135_26191.FStar_TypeChecker_Cfg.reifying)
                            }  in
                          let norm_or_whnf env2 t2 =
                            if whnf
                            then closure_as_term cfg_exclude_zeta env2 t2
                            else norm cfg_exclude_zeta env2 [] t2  in
                          let rec norm_pat env2 p =
                            match p.FStar_Syntax_Syntax.v with
                            | FStar_Syntax_Syntax.Pat_constant uu____26266 ->
                                (p, env2)
                            | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                                let uu____26297 =
                                  FStar_All.pipe_right pats
                                    (FStar_List.fold_left
                                       (fun uu____26386  ->
                                          fun uu____26387  ->
                                            match (uu____26386, uu____26387)
                                            with
                                            | ((pats1,env3),(p1,b)) ->
                                                let uu____26537 =
                                                  norm_pat env3 p1  in
                                                (match uu____26537 with
                                                 | (p2,env4) ->
                                                     (((p2, b) :: pats1),
                                                       env4))) ([], env2))
                                   in
                                (match uu____26297 with
                                 | (pats1,env3) ->
                                     ((let uu___3163_26707 = p  in
                                       {
                                         FStar_Syntax_Syntax.v =
                                           (FStar_Syntax_Syntax.Pat_cons
                                              (fv, (FStar_List.rev pats1)));
                                         FStar_Syntax_Syntax.p =
                                           (uu___3163_26707.FStar_Syntax_Syntax.p)
                                       }), env3))
                            | FStar_Syntax_Syntax.Pat_var x ->
                                let x1 =
                                  let uu___3167_26728 = x  in
                                  let uu____26729 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3167_26728.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3167_26728.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26729
                                  }  in
                                ((let uu___3170_26743 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_var x1);
                                    FStar_Syntax_Syntax.p =
                                      (uu___3170_26743.FStar_Syntax_Syntax.p)
                                  }), (dummy :: env2))
                            | FStar_Syntax_Syntax.Pat_wild x ->
                                let x1 =
                                  let uu___3174_26754 = x  in
                                  let uu____26755 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3174_26754.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3174_26754.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26755
                                  }  in
                                ((let uu___3177_26769 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_wild x1);
                                    FStar_Syntax_Syntax.p =
                                      (uu___3177_26769.FStar_Syntax_Syntax.p)
                                  }), (dummy :: env2))
                            | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                                let x1 =
                                  let uu___3183_26785 = x  in
                                  let uu____26786 =
                                    norm_or_whnf env2
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  {
                                    FStar_Syntax_Syntax.ppname =
                                      (uu___3183_26785.FStar_Syntax_Syntax.ppname);
                                    FStar_Syntax_Syntax.index =
                                      (uu___3183_26785.FStar_Syntax_Syntax.index);
                                    FStar_Syntax_Syntax.sort = uu____26786
                                  }  in
                                let t3 = norm_or_whnf env2 t2  in
                                ((let uu___3187_26801 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_dot_term
                                         (x1, t3));
                                    FStar_Syntax_Syntax.p =
                                      (uu___3187_26801.FStar_Syntax_Syntax.p)
                                  }), env2)
                             in
                          let branches1 =
                            match env1 with
                            | [] when whnf -> branches
                            | uu____26845 ->
                                FStar_All.pipe_right branches
                                  (FStar_List.map
                                     (fun branch1  ->
                                        let uu____26875 =
                                          FStar_Syntax_Subst.open_branch
                                            branch1
                                           in
                                        match uu____26875 with
                                        | (p,wopt,e) ->
                                            let uu____26895 = norm_pat env1 p
                                               in
                                            (match uu____26895 with
                                             | (p1,env2) ->
                                                 let wopt1 =
                                                   match wopt with
                                                   | FStar_Pervasives_Native.None
                                                        ->
                                                       FStar_Pervasives_Native.None
                                                   | FStar_Pervasives_Native.Some
                                                       w ->
                                                       let uu____26950 =
                                                         norm_or_whnf env2 w
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____26950
                                                    in
                                                 let e1 = norm_or_whnf env2 e
                                                    in
                                                 FStar_Syntax_Util.branch
                                                   (p1, wopt1, e1))))
                             in
                          let scrutinee1 =
                            let uu____26967 =
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
                            if uu____26967
                            then
                              norm
                                (let uu___3206_26974 = cfg1  in
                                 {
                                   FStar_TypeChecker_Cfg.steps =
                                     (let uu___3208_26977 =
                                        cfg1.FStar_TypeChecker_Cfg.steps  in
                                      {
                                        FStar_TypeChecker_Cfg.beta =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.beta);
                                        FStar_TypeChecker_Cfg.iota =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.iota);
                                        FStar_TypeChecker_Cfg.zeta =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.zeta);
                                        FStar_TypeChecker_Cfg.weak =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.weak);
                                        FStar_TypeChecker_Cfg.hnf =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.hnf);
                                        FStar_TypeChecker_Cfg.primops =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.primops);
                                        FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                          =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                        FStar_TypeChecker_Cfg.unfold_until =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.unfold_until);
                                        FStar_TypeChecker_Cfg.unfold_only =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.unfold_only);
                                        FStar_TypeChecker_Cfg.unfold_fully =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.unfold_fully);
                                        FStar_TypeChecker_Cfg.unfold_attr =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.unfold_attr);
                                        FStar_TypeChecker_Cfg.unfold_tac =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.unfold_tac);
                                        FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                          =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                        FStar_TypeChecker_Cfg.simplify =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.simplify);
                                        FStar_TypeChecker_Cfg.erase_universes
                                          =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.erase_universes);
                                        FStar_TypeChecker_Cfg.allow_unbound_universes
                                          =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                        FStar_TypeChecker_Cfg.reify_ =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.reify_);
                                        FStar_TypeChecker_Cfg.compress_uvars
                                          =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.compress_uvars);
                                        FStar_TypeChecker_Cfg.no_full_norm =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.no_full_norm);
                                        FStar_TypeChecker_Cfg.check_no_uvars
                                          =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.check_no_uvars);
                                        FStar_TypeChecker_Cfg.unmeta =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.unmeta);
                                        FStar_TypeChecker_Cfg.unascribe =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.unascribe);
                                        FStar_TypeChecker_Cfg.in_full_norm_request
                                          =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.in_full_norm_request);
                                        FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                          = false;
                                        FStar_TypeChecker_Cfg.nbe_step =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.nbe_step);
                                        FStar_TypeChecker_Cfg.for_extraction
                                          =
                                          (uu___3208_26977.FStar_TypeChecker_Cfg.for_extraction)
                                      });
                                   FStar_TypeChecker_Cfg.tcenv =
                                     (uu___3206_26974.FStar_TypeChecker_Cfg.tcenv);
                                   FStar_TypeChecker_Cfg.debug =
                                     (uu___3206_26974.FStar_TypeChecker_Cfg.debug);
                                   FStar_TypeChecker_Cfg.delta_level =
                                     (uu___3206_26974.FStar_TypeChecker_Cfg.delta_level);
                                   FStar_TypeChecker_Cfg.primitive_steps =
                                     (uu___3206_26974.FStar_TypeChecker_Cfg.primitive_steps);
                                   FStar_TypeChecker_Cfg.strong =
                                     (uu___3206_26974.FStar_TypeChecker_Cfg.strong);
                                   FStar_TypeChecker_Cfg.memoize_lazy =
                                     (uu___3206_26974.FStar_TypeChecker_Cfg.memoize_lazy);
                                   FStar_TypeChecker_Cfg.normalize_pure_lets
                                     =
                                     (uu___3206_26974.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                   FStar_TypeChecker_Cfg.reifying =
                                     (uu___3206_26974.FStar_TypeChecker_Cfg.reifying)
                                 }) scrutinee_env [] scrutinee
                            else scrutinee  in
                          let uu____26981 =
                            mk
                              (FStar_Syntax_Syntax.Tm_match
                                 (scrutinee1, branches1)) r
                             in
                          rebuild cfg1 env1 stack1 uu____26981)
                          in
                       let rec is_cons head1 =
                         let uu____27007 =
                           let uu____27008 =
                             FStar_Syntax_Subst.compress head1  in
                           uu____27008.FStar_Syntax_Syntax.n  in
                         match uu____27007 with
                         | FStar_Syntax_Syntax.Tm_uinst (h,uu____27013) ->
                             is_cons h
                         | FStar_Syntax_Syntax.Tm_constant uu____27018 ->
                             true
                         | FStar_Syntax_Syntax.Tm_fvar
                             { FStar_Syntax_Syntax.fv_name = uu____27020;
                               FStar_Syntax_Syntax.fv_delta = uu____27021;
                               FStar_Syntax_Syntax.fv_qual =
                                 FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Data_ctor );_}
                             -> true
                         | FStar_Syntax_Syntax.Tm_fvar
                             { FStar_Syntax_Syntax.fv_name = uu____27023;
                               FStar_Syntax_Syntax.fv_delta = uu____27024;
                               FStar_Syntax_Syntax.fv_qual =
                                 FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Syntax.Record_ctor
                                 uu____27025);_}
                             -> true
                         | uu____27033 -> false  in
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
                         let uu____27202 =
                           FStar_Syntax_Util.head_and_args scrutinee2  in
                         match uu____27202 with
                         | (head1,args) ->
                             (match p.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_var bv ->
                                  FStar_Util.Inl [(bv, scrutinee_orig)]
                              | FStar_Syntax_Syntax.Pat_wild bv ->
                                  FStar_Util.Inl [(bv, scrutinee_orig)]
                              | FStar_Syntax_Syntax.Pat_dot_term uu____27299
                                  -> FStar_Util.Inl []
                              | FStar_Syntax_Syntax.Pat_constant s ->
                                  (match scrutinee2.FStar_Syntax_Syntax.n
                                   with
                                   | FStar_Syntax_Syntax.Tm_constant s' when
                                       FStar_Const.eq_const s s' ->
                                       FStar_Util.Inl []
                                   | uu____27341 ->
                                       let uu____27342 =
                                         let uu____27344 = is_cons head1  in
                                         Prims.op_Negation uu____27344  in
                                       FStar_Util.Inr uu____27342)
                              | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                                  let uu____27373 =
                                    let uu____27374 =
                                      FStar_Syntax_Util.un_uinst head1  in
                                    uu____27374.FStar_Syntax_Syntax.n  in
                                  (match uu____27373 with
                                   | FStar_Syntax_Syntax.Tm_fvar fv' when
                                       FStar_Syntax_Syntax.fv_eq fv fv' ->
                                       matches_args [] args arg_pats
                                   | uu____27393 ->
                                       let uu____27394 =
                                         let uu____27396 = is_cons head1  in
                                         Prims.op_Negation uu____27396  in
                                       FStar_Util.Inr uu____27394))
                       
                       and matches_args out a p =
                         match (a, p) with
                         | ([],[]) -> FStar_Util.Inl out
                         | ((t2,uu____27487)::rest_a,(p1,uu____27490)::rest_p)
                             ->
                             let uu____27549 = matches_pat t2 p1  in
                             (match uu____27549 with
                              | FStar_Util.Inl s ->
                                  matches_args (FStar_List.append out s)
                                    rest_a rest_p
                              | m -> m)
                         | uu____27602 -> FStar_Util.Inr false
                        in
                       let rec matches scrutinee1 p =
                         match p with
                         | [] -> norm_and_rebuild_match ()
                         | (p1,wopt,b)::rest ->
                             let uu____27725 = matches_pat scrutinee1 p1  in
                             (match uu____27725 with
                              | FStar_Util.Inr (false ) ->
                                  matches scrutinee1 rest
                              | FStar_Util.Inr (true ) ->
                                  norm_and_rebuild_match ()
                              | FStar_Util.Inl s ->
                                  (FStar_TypeChecker_Cfg.log cfg1
                                     (fun uu____27771  ->
                                        let uu____27772 =
                                          FStar_Syntax_Print.pat_to_string p1
                                           in
                                        let uu____27774 =
                                          let uu____27776 =
                                            FStar_List.map
                                              (fun uu____27788  ->
                                                 match uu____27788 with
                                                 | (uu____27794,t2) ->
                                                     FStar_Syntax_Print.term_to_string
                                                       t2) s
                                             in
                                          FStar_All.pipe_right uu____27776
                                            (FStar_String.concat "; ")
                                           in
                                        FStar_Util.print2
                                          "Matches pattern %s with subst = %s\n"
                                          uu____27772 uu____27774);
                                   (let env0 = env1  in
                                    let env2 =
                                      FStar_List.fold_left
                                        (fun env2  ->
                                           fun uu____27830  ->
                                             match uu____27830 with
                                             | (bv,t2) ->
                                                 let uu____27853 =
                                                   let uu____27860 =
                                                     let uu____27863 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         bv
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____27863
                                                      in
                                                   let uu____27864 =
                                                     let uu____27865 =
                                                       let uu____27897 =
                                                         FStar_Util.mk_ref
                                                           (FStar_Pervasives_Native.Some
                                                              ([], t2))
                                                          in
                                                       ([], t2, uu____27897,
                                                         false)
                                                        in
                                                     Clos uu____27865  in
                                                   (uu____27860, uu____27864)
                                                    in
                                                 uu____27853 :: env2) env1 s
                                       in
                                    let uu____27990 =
                                      guard_when_clause wopt b rest  in
                                    norm cfg1 env2 stack1 uu____27990)))
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
            (fun uu____28023  ->
               let uu____28024 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____28024);
          (let uu____28027 = is_nbe_request s  in
           if uu____28027
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____28033  ->
                   let uu____28034 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____28034);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____28040  ->
                   let uu____28041 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____28041);
              (let uu____28044 =
                 FStar_Util.record_time (fun uu____28051  -> nbe_eval c s t)
                  in
               match uu____28044 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____28060  ->
                         let uu____28061 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____28063 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____28061 uu____28063);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____28071  ->
                   let uu____28072 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____28072);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____28078  ->
                   let uu____28079 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____28079);
              (let uu____28082 =
                 FStar_Util.record_time (fun uu____28089  -> norm c [] [] t)
                  in
               match uu____28082 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____28104  ->
                         let uu____28105 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____28107 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____28105 uu____28107);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____28126 =
          let uu____28130 =
            let uu____28132 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____28132  in
          FStar_Pervasives_Native.Some uu____28130  in
        FStar_Profiling.profile
          (fun uu____28135  -> normalize_with_primitive_steps [] s e t)
          uu____28126 "FStar.TypeChecker.Normalize"
  
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
          (fun uu____28157  ->
             let uu____28158 = FStar_Syntax_Print.comp_to_string c  in
             FStar_Util.print1 "Starting normalizer for computation (%s) {\n"
               uu____28158);
        FStar_TypeChecker_Cfg.log_top cfg
          (fun uu____28164  ->
             let uu____28165 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
             FStar_Util.print1 ">>> cfg = %s\n" uu____28165);
        (let uu____28168 =
           FStar_Util.record_time (fun uu____28175  -> norm_comp cfg [] c)
            in
         match uu____28168 with
         | (c1,ms) ->
             (FStar_TypeChecker_Cfg.log_top cfg
                (fun uu____28190  ->
                   let uu____28191 = FStar_Syntax_Print.comp_to_string c1  in
                   let uu____28193 = FStar_Util.string_of_int ms  in
                   FStar_Util.print2
                     "}\nNormalization result = (%s) in %s ms\n" uu____28191
                     uu____28193);
              c1))
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____28207 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____28207 [] u
  
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
      let uu____28229 = normalize steps env t  in
      FStar_TypeChecker_Env.non_informative env uu____28229
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____28241 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info_norm env t ->
          let uu___3376_28260 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3376_28260.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3376_28260.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name env
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____28267 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info_norm env ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____28267
          then
            let ct1 =
              let uu____28271 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____28271 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____28278 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____28278
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3386_28285 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3386_28285.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3386_28285.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3386_28285.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 = FStar_TypeChecker_Env.unfold_effect_abbrev env c
                     in
                  let uu___3390_28287 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3390_28287.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3390_28287.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3390_28287.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3390_28287.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3393_28288 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3393_28288.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3393_28288.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____28291 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      let uu____28303 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info_norm env lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____28303
      then
        let uu____28306 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____28306 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3401_28310 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3401_28310.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3401_28310.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3401_28310.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3408_28329  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3407_28332 ->
            ((let uu____28334 =
                let uu____28340 =
                  let uu____28342 = FStar_Util.message_of_exn uu___3407_28332
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____28342
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____28340)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____28334);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3418_28361  ->
             match () with
             | () ->
                 let uu____28362 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____28362 [] c) ()
        with
        | uu___3417_28371 ->
            ((let uu____28373 =
                let uu____28379 =
                  let uu____28381 = FStar_Util.message_of_exn uu___3417_28371
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____28381
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____28379)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____28373);
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
                   let uu____28430 =
                     let uu____28431 =
                       let uu____28438 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____28438)  in
                     FStar_Syntax_Syntax.Tm_refine uu____28431  in
                   mk uu____28430 t01.FStar_Syntax_Syntax.pos
               | uu____28443 -> t2)
          | uu____28444 -> t2  in
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
        let uu____28538 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____28538 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____28575 ->
                 let uu____28584 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____28584 with
                  | (actuals,uu____28594,uu____28595) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____28615 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____28615 with
                         | (binders,args) ->
                             let uu____28626 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____28626
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
      | uu____28641 ->
          let uu____28642 = FStar_Syntax_Util.head_and_args t  in
          (match uu____28642 with
           | (head1,args) ->
               let uu____28685 =
                 let uu____28686 = FStar_Syntax_Subst.compress head1  in
                 uu____28686.FStar_Syntax_Syntax.n  in
               (match uu____28685 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____28707 =
                      let uu____28722 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____28722  in
                    (match uu____28707 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____28762 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3488_28770 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3488_28770.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3488_28770.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3488_28770.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3488_28770.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3488_28770.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3488_28770.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3488_28770.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3488_28770.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3488_28770.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3488_28770.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3488_28770.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3488_28770.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3488_28770.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3488_28770.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3488_28770.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3488_28770.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___3488_28770.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3488_28770.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3488_28770.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3488_28770.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3488_28770.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3488_28770.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3488_28770.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3488_28770.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3488_28770.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3488_28770.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3488_28770.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3488_28770.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3488_28770.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3488_28770.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3488_28770.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3488_28770.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3488_28770.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3488_28770.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3488_28770.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3488_28770.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3488_28770.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3488_28770.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3488_28770.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3488_28770.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3488_28770.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3488_28770.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3488_28770.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____28762 with
                            | (uu____28773,ty,uu____28775) ->
                                eta_expand_with_type env t ty))
                | uu____28776 ->
                    let uu____28777 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3495_28785 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3495_28785.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3495_28785.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3495_28785.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3495_28785.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3495_28785.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3495_28785.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3495_28785.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3495_28785.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3495_28785.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3495_28785.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3495_28785.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3495_28785.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3495_28785.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3495_28785.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3495_28785.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3495_28785.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.use_eq_strict =
                             (uu___3495_28785.FStar_TypeChecker_Env.use_eq_strict);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3495_28785.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3495_28785.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3495_28785.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3495_28785.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3495_28785.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3495_28785.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3495_28785.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3495_28785.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3495_28785.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3495_28785.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3495_28785.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3495_28785.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3495_28785.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3495_28785.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3495_28785.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3495_28785.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3495_28785.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3495_28785.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3495_28785.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3495_28785.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3495_28785.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3495_28785.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3495_28785.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3495_28785.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3495_28785.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3495_28785.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____28777 with
                     | (uu____28788,ty,uu____28790) ->
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
      let uu___3507_28872 = x  in
      let uu____28873 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3507_28872.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3507_28872.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____28873
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____28876 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____28900 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____28901 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____28902 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____28903 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____28910 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____28911 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____28912 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3533_28946 = rc  in
          let uu____28947 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____28956 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3533_28946.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____28947;
            FStar_Syntax_Syntax.residual_flags = uu____28956
          }  in
        let uu____28959 =
          let uu____28960 =
            let uu____28979 = elim_delayed_subst_binders bs  in
            let uu____28988 = elim_delayed_subst_term t2  in
            let uu____28991 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____28979, uu____28988, uu____28991)  in
          FStar_Syntax_Syntax.Tm_abs uu____28960  in
        mk1 uu____28959
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____29028 =
          let uu____29029 =
            let uu____29044 = elim_delayed_subst_binders bs  in
            let uu____29053 = elim_delayed_subst_comp c  in
            (uu____29044, uu____29053)  in
          FStar_Syntax_Syntax.Tm_arrow uu____29029  in
        mk1 uu____29028
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____29072 =
          let uu____29073 =
            let uu____29080 = elim_bv bv  in
            let uu____29081 = elim_delayed_subst_term phi  in
            (uu____29080, uu____29081)  in
          FStar_Syntax_Syntax.Tm_refine uu____29073  in
        mk1 uu____29072
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____29112 =
          let uu____29113 =
            let uu____29130 = elim_delayed_subst_term t2  in
            let uu____29133 = elim_delayed_subst_args args  in
            (uu____29130, uu____29133)  in
          FStar_Syntax_Syntax.Tm_app uu____29113  in
        mk1 uu____29112
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3555_29205 = p  in
              let uu____29206 =
                let uu____29207 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____29207  in
              {
                FStar_Syntax_Syntax.v = uu____29206;
                FStar_Syntax_Syntax.p =
                  (uu___3555_29205.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3559_29209 = p  in
              let uu____29210 =
                let uu____29211 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____29211  in
              {
                FStar_Syntax_Syntax.v = uu____29210;
                FStar_Syntax_Syntax.p =
                  (uu___3559_29209.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3565_29218 = p  in
              let uu____29219 =
                let uu____29220 =
                  let uu____29227 = elim_bv x  in
                  let uu____29228 = elim_delayed_subst_term t0  in
                  (uu____29227, uu____29228)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____29220  in
              {
                FStar_Syntax_Syntax.v = uu____29219;
                FStar_Syntax_Syntax.p =
                  (uu___3565_29218.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3571_29253 = p  in
              let uu____29254 =
                let uu____29255 =
                  let uu____29269 =
                    FStar_List.map
                      (fun uu____29295  ->
                         match uu____29295 with
                         | (x,b) ->
                             let uu____29312 = elim_pat x  in
                             (uu____29312, b)) pats
                     in
                  (fv, uu____29269)  in
                FStar_Syntax_Syntax.Pat_cons uu____29255  in
              {
                FStar_Syntax_Syntax.v = uu____29254;
                FStar_Syntax_Syntax.p =
                  (uu___3571_29253.FStar_Syntax_Syntax.p)
              }
          | uu____29327 -> p  in
        let elim_branch uu____29351 =
          match uu____29351 with
          | (pat,wopt,t3) ->
              let uu____29377 = elim_pat pat  in
              let uu____29380 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____29383 = elim_delayed_subst_term t3  in
              (uu____29377, uu____29380, uu____29383)
           in
        let uu____29388 =
          let uu____29389 =
            let uu____29412 = elim_delayed_subst_term t2  in
            let uu____29415 = FStar_List.map elim_branch branches  in
            (uu____29412, uu____29415)  in
          FStar_Syntax_Syntax.Tm_match uu____29389  in
        mk1 uu____29388
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____29546 =
          match uu____29546 with
          | (tc,topt) ->
              let uu____29581 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____29591 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____29591
                | FStar_Util.Inr c ->
                    let uu____29593 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____29593
                 in
              let uu____29594 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____29581, uu____29594)
           in
        let uu____29603 =
          let uu____29604 =
            let uu____29631 = elim_delayed_subst_term t2  in
            let uu____29634 = elim_ascription a  in
            (uu____29631, uu____29634, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____29604  in
        mk1 uu____29603
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3601_29697 = lb  in
          let uu____29698 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____29701 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3601_29697.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3601_29697.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____29698;
            FStar_Syntax_Syntax.lbeff =
              (uu___3601_29697.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____29701;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3601_29697.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3601_29697.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____29704 =
          let uu____29705 =
            let uu____29719 =
              let uu____29727 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____29727)  in
            let uu____29739 = elim_delayed_subst_term t2  in
            (uu____29719, uu____29739)  in
          FStar_Syntax_Syntax.Tm_let uu____29705  in
        mk1 uu____29704
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____29784 =
          let uu____29785 =
            let uu____29792 = elim_delayed_subst_term tm  in
            (uu____29792, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____29785  in
        mk1 uu____29784
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____29803 =
          let uu____29804 =
            let uu____29811 = elim_delayed_subst_term t2  in
            let uu____29814 = elim_delayed_subst_meta md  in
            (uu____29811, uu____29814)  in
          FStar_Syntax_Syntax.Tm_meta uu____29804  in
        mk1 uu____29803

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_29823  ->
         match uu___17_29823 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____29827 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____29827
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
        let uu____29850 =
          let uu____29851 =
            let uu____29860 = elim_delayed_subst_term t  in
            (uu____29860, uopt)  in
          FStar_Syntax_Syntax.Total uu____29851  in
        mk1 uu____29850
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____29877 =
          let uu____29878 =
            let uu____29887 = elim_delayed_subst_term t  in
            (uu____29887, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____29878  in
        mk1 uu____29877
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3634_29896 = ct  in
          let uu____29897 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____29900 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____29911 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3634_29896.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3634_29896.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____29897;
            FStar_Syntax_Syntax.effect_args = uu____29900;
            FStar_Syntax_Syntax.flags = uu____29911
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_29914  ->
    match uu___18_29914 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____29949 =
          let uu____29970 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____29979 = FStar_List.map elim_delayed_subst_args args  in
          (uu____29970, uu____29979)  in
        FStar_Syntax_Syntax.Meta_pattern uu____29949
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____30034 =
          let uu____30041 = elim_delayed_subst_term t  in (m, uu____30041)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____30034
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____30053 =
          let uu____30062 = elim_delayed_subst_term t  in
          (m1, m2, uu____30062)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____30053
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
      (fun uu____30095  ->
         match uu____30095 with
         | (t,q) ->
             let uu____30114 = elim_delayed_subst_term t  in (uu____30114, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____30142  ->
         match uu____30142 with
         | (x,q) ->
             let uu____30161 =
               let uu___3660_30162 = x  in
               let uu____30163 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3660_30162.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3660_30162.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____30163
               }  in
             (uu____30161, q)) bs

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
            | (uu____30271,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____30303,FStar_Util.Inl t) ->
                let uu____30325 =
                  let uu____30332 =
                    let uu____30333 =
                      let uu____30348 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____30348)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____30333  in
                  FStar_Syntax_Syntax.mk uu____30332  in
                uu____30325 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____30361 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____30361 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____30393 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____30466 ->
                    let uu____30467 =
                      let uu____30476 =
                        let uu____30477 = FStar_Syntax_Subst.compress t4  in
                        uu____30477.FStar_Syntax_Syntax.n  in
                      (uu____30476, tc)  in
                    (match uu____30467 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____30506) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____30553) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____30598,FStar_Util.Inl uu____30599) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____30630 -> failwith "Impossible")
                 in
              (match uu____30393 with
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
          let uu____30769 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____30769 with
          | (univ_names1,binders1,tc) ->
              let uu____30843 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____30843)
  
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
          let uu____30897 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____30897 with
          | (univ_names1,binders1,tc) ->
              let uu____30971 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____30971)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____31013 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____31013 with
           | (univ_names1,binders1,typ1) ->
               let uu___3743_31053 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3743_31053.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3743_31053.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3743_31053.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3743_31053.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3743_31053.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3749_31068 = s  in
          let uu____31069 =
            let uu____31070 =
              let uu____31079 = FStar_List.map (elim_uvars env) sigs  in
              (uu____31079, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____31070  in
          {
            FStar_Syntax_Syntax.sigel = uu____31069;
            FStar_Syntax_Syntax.sigrng =
              (uu___3749_31068.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3749_31068.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3749_31068.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3749_31068.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3749_31068.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____31098 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____31098 with
           | (univ_names1,uu____31122,typ1) ->
               let uu___3763_31144 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3763_31144.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3763_31144.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3763_31144.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3763_31144.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3763_31144.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____31151 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____31151 with
           | (univ_names1,uu____31175,typ1) ->
               let uu___3774_31197 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3774_31197.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3774_31197.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3774_31197.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3774_31197.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3774_31197.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____31227 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____31227 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____31252 =
                            let uu____31253 =
                              let uu____31254 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____31254  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____31253
                             in
                          elim_delayed_subst_term uu____31252  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3790_31257 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3790_31257.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3790_31257.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3790_31257.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3790_31257.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3793_31258 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3793_31258.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3793_31258.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3793_31258.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3793_31258.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3793_31258.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3797_31265 = s  in
          let uu____31266 =
            let uu____31267 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____31267  in
          {
            FStar_Syntax_Syntax.sigel = uu____31266;
            FStar_Syntax_Syntax.sigrng =
              (uu___3797_31265.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3797_31265.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3797_31265.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3797_31265.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3797_31265.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____31271 = elim_uvars_aux_t env us [] t  in
          (match uu____31271 with
           | (us1,uu____31295,t1) ->
               let uu___3808_31317 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3808_31317.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3808_31317.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3808_31317.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3808_31317.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3808_31317.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____31319 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____31319 with
           | (univs1,binders,uu____31338) ->
               let uu____31359 =
                 let uu____31364 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____31364 with
                 | (univs_opening,univs2) ->
                     let uu____31387 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____31387)
                  in
               (match uu____31359 with
                | (univs_opening,univs_closing) ->
                    let uu____31390 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____31396 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____31397 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____31396, uu____31397)  in
                    (match uu____31390 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____31423 =
                           match uu____31423 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____31441 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____31441 with
                                | (us1,t1) ->
                                    let uu____31452 =
                                      let uu____31461 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____31466 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____31461, uu____31466)  in
                                    (match uu____31452 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____31489 =
                                           let uu____31498 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____31503 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____31498, uu____31503)  in
                                         (match uu____31489 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____31527 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____31527
                                                 in
                                              let uu____31528 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____31528 with
                                               | (uu____31555,uu____31556,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____31579 =
                                                       let uu____31580 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____31580
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____31579
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____31589 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____31589 with
                           | (uu____31608,uu____31609,t1) -> t1  in
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
                             | uu____31685 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____31712 =
                               let uu____31713 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____31713.FStar_Syntax_Syntax.n  in
                             match uu____31712 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____31772 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____31806 =
                               let uu____31807 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____31807.FStar_Syntax_Syntax.n  in
                             match uu____31806 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____31830) ->
                                 let uu____31855 = destruct_action_body body
                                    in
                                 (match uu____31855 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____31904 ->
                                 let uu____31905 = destruct_action_body t  in
                                 (match uu____31905 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____31960 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____31960 with
                           | (action_univs,t) ->
                               let uu____31969 = destruct_action_typ_templ t
                                  in
                               (match uu____31969 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3892_32016 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3892_32016.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3892_32016.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3895_32018 = ed  in
                           let uu____32019 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____32020 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____32021 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3895_32018.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3895_32018.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____32019;
                             FStar_Syntax_Syntax.combinators = uu____32020;
                             FStar_Syntax_Syntax.actions = uu____32021;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3895_32018.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3898_32024 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3898_32024.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3898_32024.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3898_32024.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3898_32024.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3898_32024.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_32045 =
            match uu___19_32045 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____32076 = elim_uvars_aux_t env us [] t  in
                (match uu____32076 with
                 | (us1,uu____32108,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3913_32139 = sub_eff  in
            let uu____32140 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____32143 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3913_32139.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3913_32139.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____32140;
              FStar_Syntax_Syntax.lift = uu____32143
            }  in
          let uu___3916_32146 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3916_32146.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3916_32146.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3916_32146.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3916_32146.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3916_32146.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____32156 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____32156 with
           | (univ_names1,binders1,comp1) ->
               let uu___3929_32196 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3929_32196.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3929_32196.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3929_32196.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3929_32196.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3929_32196.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____32199 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____32200 -> s
      | FStar_Syntax_Syntax.Sig_polymonadic_bind (m,n1,p,(us_t,t),(us_ty,ty))
          ->
          let uu____32230 = elim_uvars_aux_t env us_t [] t  in
          (match uu____32230 with
           | (us_t1,uu____32254,t1) ->
               let uu____32276 = elim_uvars_aux_t env us_ty [] ty  in
               (match uu____32276 with
                | (us_ty1,uu____32300,ty1) ->
                    let uu___3954_32322 = s  in
                    {
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_polymonadic_bind
                           (m, n1, p, (us_t1, t1), (us_ty1, ty1)));
                      FStar_Syntax_Syntax.sigrng =
                        (uu___3954_32322.FStar_Syntax_Syntax.sigrng);
                      FStar_Syntax_Syntax.sigquals =
                        (uu___3954_32322.FStar_Syntax_Syntax.sigquals);
                      FStar_Syntax_Syntax.sigmeta =
                        (uu___3954_32322.FStar_Syntax_Syntax.sigmeta);
                      FStar_Syntax_Syntax.sigattrs =
                        (uu___3954_32322.FStar_Syntax_Syntax.sigattrs);
                      FStar_Syntax_Syntax.sigopts =
                        (uu___3954_32322.FStar_Syntax_Syntax.sigopts)
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
        let uu____32373 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____32373 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____32395 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____32395 with
             | (uu____32402,head_def) ->
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
      let uu____32408 = FStar_Syntax_Util.head_and_args t  in
      match uu____32408 with
      | (head1,args) ->
          let uu____32453 =
            let uu____32454 = FStar_Syntax_Subst.compress head1  in
            uu____32454.FStar_Syntax_Syntax.n  in
          (match uu____32453 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____32461;
                  FStar_Syntax_Syntax.vars = uu____32462;_},us)
               -> aux fv us args
           | uu____32468 -> FStar_Pervasives_Native.None)
  