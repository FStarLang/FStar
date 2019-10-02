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
  
let rec (env_to_string :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> Prims.string)
  =
  fun env  ->
    let uu____1034 =
      FStar_List.map
        (fun uu____1050  ->
           match uu____1050 with
           | (bopt,c) ->
               let uu____1064 =
                 match bopt with
                 | FStar_Pervasives_Native.None  -> "."
                 | FStar_Pervasives_Native.Some x ->
                     FStar_Syntax_Print.binder_to_string x
                  in
               let uu____1069 = closure_to_string c  in
               FStar_Util.format2 "(%s, %s)" uu____1064 uu____1069) env
       in
    FStar_All.pipe_right uu____1034 (FStar_String.concat "; ")

and (closure_to_string : closure -> Prims.string) =
  fun uu___1_1077  ->
    match uu___1_1077 with
    | Clos (env,t,uu____1081,uu____1082) ->
        let uu____1129 =
          FStar_All.pipe_right (FStar_List.length env)
            FStar_Util.string_of_int
           in
        let uu____1139 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format2 "(env=%s elts; %s)" uu____1129 uu____1139
    | Univ uu____1142 -> "Univ"
    | Dummy  -> "dummy"

let (stack_elt_to_string : stack_elt -> Prims.string) =
  fun uu___2_1151  ->
    match uu___2_1151 with
    | Arg (c,uu____1154,uu____1155) ->
        let uu____1156 = closure_to_string c  in
        FStar_Util.format1 "Closure %s" uu____1156
    | MemoLazy uu____1159 -> "MemoLazy"
    | Abs (uu____1167,bs,uu____1169,uu____1170,uu____1171) ->
        let uu____1176 =
          FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length bs)
           in
        FStar_Util.format1 "Abs %s" uu____1176
    | UnivArgs uu____1187 -> "UnivArgs"
    | Match uu____1195 -> "Match"
    | App (uu____1205,t,uu____1207,uu____1208) ->
        let uu____1209 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "App %s" uu____1209
    | Meta (uu____1212,m,uu____1214) -> "Meta"
    | Let uu____1216 -> "Let"
    | Cfg uu____1226 -> "Cfg"
    | Debug (t,uu____1229) ->
        let uu____1230 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.format1 "Debug %s" uu____1230
  
let (stack_to_string : stack_elt Prims.list -> Prims.string) =
  fun s  ->
    let uu____1244 = FStar_List.map stack_elt_to_string s  in
    FStar_All.pipe_right uu____1244 (FStar_String.concat "; ")
  
let is_empty : 'Auu____1259 . 'Auu____1259 Prims.list -> Prims.bool =
  fun uu___3_1267  ->
    match uu___3_1267 with | [] -> true | uu____1271 -> false
  
let (lookup_bvar :
  (FStar_Syntax_Syntax.binder FStar_Pervasives_Native.option * closure)
    Prims.list -> FStar_Syntax_Syntax.bv -> closure)
  =
  fun env  ->
    fun x  ->
      try
        (fun uu___114_1304  ->
           match () with
           | () ->
               let uu____1305 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1305) ()
      with
      | uu___113_1322 ->
          let uu____1323 =
            let uu____1325 = FStar_Syntax_Print.db_to_string x  in
            let uu____1327 = env_to_string env  in
            FStar_Util.format2 "Failed to find %s\nEnv is %s\n" uu____1325
              uu____1327
             in
          failwith uu____1323
  
let (downgrade_ghost_effect_name :
  FStar_Ident.lident -> FStar_Ident.lident FStar_Pervasives_Native.option) =
  fun l  ->
    let uu____1338 =
      FStar_Ident.lid_equals l FStar_Parser_Const.effect_Ghost_lid  in
    if uu____1338
    then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Pure_lid
    else
      (let uu____1345 =
         FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid  in
       if uu____1345
       then FStar_Pervasives_Native.Some FStar_Parser_Const.effect_Tot_lid
       else
         (let uu____1352 =
            FStar_Ident.lid_equals l FStar_Parser_Const.effect_GHOST_lid  in
          if uu____1352
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
          let uu____1390 =
            FStar_List.fold_left
              (fun uu____1416  ->
                 fun u1  ->
                   match uu____1416 with
                   | (cur_kernel,cur_max,out) ->
                       let uu____1441 = FStar_Syntax_Util.univ_kernel u1  in
                       (match uu____1441 with
                        | (k_u,n1) ->
                            let uu____1459 =
                              FStar_Syntax_Util.eq_univs cur_kernel k_u  in
                            if uu____1459
                            then (cur_kernel, u1, out)
                            else (k_u, u1, (cur_max :: out))))
              (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero, [])
              us1
             in
          match uu____1390 with
          | (uu____1480,u1,out) -> FStar_List.rev (u1 :: out)  in
        let rec aux u1 =
          let u2 = FStar_Syntax_Subst.compress_univ u1  in
          match u2 with
          | FStar_Syntax_Syntax.U_bvar x ->
              (try
                 (fun uu___148_1506  ->
                    match () with
                    | () ->
                        let uu____1509 =
                          let uu____1510 = FStar_List.nth env x  in
                          FStar_Pervasives_Native.snd uu____1510  in
                        (match uu____1509 with
                         | Univ u3 ->
                             ((let uu____1529 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      cfg.FStar_TypeChecker_Cfg.tcenv)
                                   (FStar_Options.Other "univ_norm")
                                  in
                               if uu____1529
                               then
                                 let uu____1534 =
                                   FStar_Syntax_Print.univ_to_string u3  in
                                 FStar_Util.print1
                                   "Univ (in norm_universe): %s\n" uu____1534
                               else ());
                              aux u3)
                         | Dummy  -> [u2]
                         | uu____1539 ->
                             let uu____1540 =
                               let uu____1542 = FStar_Util.string_of_int x
                                  in
                               FStar_Util.format1
                                 "Impossible: universe variable u@%s bound to a term"
                                 uu____1542
                                in
                             failwith uu____1540)) ()
               with
               | uu____1552 ->
                   if
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                   then [FStar_Syntax_Syntax.U_unknown]
                   else
                     (let uu____1558 =
                        let uu____1560 = FStar_Util.string_of_int x  in
                        FStar_String.op_Hat "Universe variable not found: u@"
                          uu____1560
                         in
                      failwith uu____1558))
          | FStar_Syntax_Syntax.U_unif uu____1565 when
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
              -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_zero  -> [u2]
          | FStar_Syntax_Syntax.U_unif uu____1574 -> [u2]
          | FStar_Syntax_Syntax.U_name uu____1583 -> [u2]
          | FStar_Syntax_Syntax.U_unknown  -> [u2]
          | FStar_Syntax_Syntax.U_max [] -> [FStar_Syntax_Syntax.U_zero]
          | FStar_Syntax_Syntax.U_max us ->
              let us1 =
                let uu____1590 = FStar_List.collect aux us  in
                FStar_All.pipe_right uu____1590 norm_univs  in
              (match us1 with
               | u_k::hd1::rest ->
                   let rest1 = hd1 :: rest  in
                   let uu____1607 = FStar_Syntax_Util.univ_kernel u_k  in
                   (match uu____1607 with
                    | (FStar_Syntax_Syntax.U_zero ,n1) ->
                        let uu____1618 =
                          FStar_All.pipe_right rest1
                            (FStar_List.for_all
                               (fun u3  ->
                                  let uu____1628 =
                                    FStar_Syntax_Util.univ_kernel u3  in
                                  match uu____1628 with
                                  | (uu____1635,m) -> n1 <= m))
                           in
                        if uu____1618 then rest1 else us1
                    | uu____1644 -> us1)
               | uu____1650 -> us1)
          | FStar_Syntax_Syntax.U_succ u3 ->
              let uu____1654 = aux u3  in
              FStar_List.map (fun _1657  -> FStar_Syntax_Syntax.U_succ _1657)
                uu____1654
           in
        if
          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
        then FStar_Syntax_Syntax.U_unknown
        else
          (let uu____1661 = aux u  in
           match uu____1661 with
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
            (fun uu____1830  ->
               let uu____1831 = FStar_Syntax_Print.tag_of_term t  in
               let uu____1833 = env_to_string env  in
               let uu____1835 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print3 "\n>>> %s (env=%s) Closure_as_term %s\n"
                 uu____1831 uu____1833 uu____1835);
          (match env with
           | [] when
               FStar_All.pipe_left Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
               -> rebuild_closure cfg env stack t
           | uu____1848 ->
               (match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_delayed uu____1851 ->
                    let uu____1874 = FStar_Syntax_Subst.compress t  in
                    inline_closure_env cfg env stack uu____1874
                | FStar_Syntax_Syntax.Tm_unknown  ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_constant uu____1875 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_name uu____1876 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_lazy uu____1877 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_fvar uu____1878 ->
                    rebuild_closure cfg env stack t
                | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let t1 = FStar_Syntax_Subst.compress t  in
                      (match t1.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_uvar uu____1903 ->
                           let uu____1916 =
                             let uu____1918 =
                               FStar_Range.string_of_range
                                 t1.FStar_Syntax_Syntax.pos
                                in
                             let uu____1920 =
                               FStar_Syntax_Print.term_to_string t1  in
                             FStar_Util.format2
                               "(%s): CheckNoUvars: Unexpected unification variable remains: %s"
                               uu____1918 uu____1920
                              in
                           failwith uu____1916
                       | uu____1925 -> inline_closure_env cfg env stack t1)
                    else
                      (let s' =
                         FStar_All.pipe_right (FStar_Pervasives_Native.fst s)
                           (FStar_List.map
                              (fun s1  ->
                                 FStar_All.pipe_right s1
                                   (FStar_List.map
                                      (fun uu___4_1961  ->
                                         match uu___4_1961 with
                                         | FStar_Syntax_Syntax.NT (x,t1) ->
                                             let uu____1968 =
                                               let uu____1975 =
                                                 inline_closure_env cfg env
                                                   [] t1
                                                  in
                                               (x, uu____1975)  in
                                             FStar_Syntax_Syntax.NT
                                               uu____1968
                                         | FStar_Syntax_Syntax.NM (x,i) ->
                                             let x_i =
                                               FStar_Syntax_Syntax.bv_to_tm
                                                 (let uu___242_1987 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___242_1987.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___242_1987.FStar_Syntax_Syntax.sort)
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
                                              | uu____1993 ->
                                                  FStar_Syntax_Syntax.NT
                                                    (x, t1))
                                         | uu____1996 ->
                                             failwith
                                               "Impossible: subst invariant of uvar nodes"))))
                          in
                       let t1 =
                         let uu___251_2001 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___251_2001.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___251_2001.FStar_Syntax_Syntax.vars)
                         }  in
                       rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_type u ->
                    let t1 =
                      let uu____2022 =
                        let uu____2023 = norm_universe cfg env u  in
                        FStar_Syntax_Syntax.Tm_type uu____2023  in
                      mk uu____2022 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
                    let t1 =
                      let uu____2031 =
                        FStar_List.map (norm_universe cfg env) us  in
                      FStar_Syntax_Syntax.mk_Tm_uinst t' uu____2031  in
                    rebuild_closure cfg env stack t1
                | FStar_Syntax_Syntax.Tm_bvar x ->
                    let uu____2033 = lookup_bvar env x  in
                    (match uu____2033 with
                     | Univ uu____2036 ->
                         failwith
                           "Impossible: term variable is bound to a universe"
                     | Dummy  ->
                         let x1 =
                           let uu___267_2041 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___267_2041.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___267_2041.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort =
                               FStar_Syntax_Syntax.tun
                           }  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_bvar x1)
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1
                     | Clos (env1,t0,uu____2047,uu____2048) ->
                         inline_closure_env cfg env1 stack t0)
                | FStar_Syntax_Syntax.Tm_app (head1,args) ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____2139  ->
                              fun stack1  ->
                                match uu____2139 with
                                | (a,aq) ->
                                    let uu____2151 =
                                      let uu____2152 =
                                        let uu____2159 =
                                          let uu____2160 =
                                            let uu____2192 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____2192, false)  in
                                          Clos uu____2160  in
                                        (uu____2159, aq,
                                          (t.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____2152  in
                                    uu____2151 :: stack1) args)
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
                    let uu____2360 = close_binders cfg env bs  in
                    (match uu____2360 with
                     | (bs1,env') ->
                         let c1 = close_comp cfg env' c  in
                         let t1 =
                           mk (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env stack t1)
                | FStar_Syntax_Syntax.Tm_refine (x,uu____2410) when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.for_extraction
                    ->
                    inline_closure_env cfg env stack
                      x.FStar_Syntax_Syntax.sort
                | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
                    let uu____2421 =
                      let uu____2434 =
                        let uu____2443 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____2443]  in
                      close_binders cfg env uu____2434  in
                    (match uu____2421 with
                     | (x1,env1) ->
                         let phi1 = non_tail_inline_closure_env cfg env1 phi
                            in
                         let t1 =
                           let uu____2488 =
                             let uu____2489 =
                               let uu____2496 =
                                 let uu____2497 = FStar_List.hd x1  in
                                 FStar_All.pipe_right uu____2497
                                   FStar_Pervasives_Native.fst
                                  in
                               (uu____2496, phi1)  in
                             FStar_Syntax_Syntax.Tm_refine uu____2489  in
                           mk uu____2488 t.FStar_Syntax_Syntax.pos  in
                         rebuild_closure cfg env1 stack t1)
                | FStar_Syntax_Syntax.Tm_ascribed (t1,(annot,tacopt),lopt) ->
                    let annot1 =
                      match annot with
                      | FStar_Util.Inl t2 ->
                          let uu____2596 =
                            non_tail_inline_closure_env cfg env t2  in
                          FStar_Util.Inl uu____2596
                      | FStar_Util.Inr c ->
                          let uu____2610 = close_comp cfg env c  in
                          FStar_Util.Inr uu____2610
                       in
                    let tacopt1 =
                      FStar_Util.map_opt tacopt
                        (non_tail_inline_closure_env cfg env)
                       in
                    let t2 =
                      let uu____2629 =
                        let uu____2630 =
                          let uu____2657 =
                            non_tail_inline_closure_env cfg env t1  in
                          (uu____2657, (annot1, tacopt1), lopt)  in
                        FStar_Syntax_Syntax.Tm_ascribed uu____2630  in
                      mk uu____2629 t.FStar_Syntax_Syntax.pos  in
                    rebuild_closure cfg env stack t2
                | FStar_Syntax_Syntax.Tm_quoted (t',qi) ->
                    let t1 =
                      match qi.FStar_Syntax_Syntax.qkind with
                      | FStar_Syntax_Syntax.Quote_dynamic  ->
                          let uu____2703 =
                            let uu____2704 =
                              let uu____2711 =
                                non_tail_inline_closure_env cfg env t'  in
                              (uu____2711, qi)  in
                            FStar_Syntax_Syntax.Tm_quoted uu____2704  in
                          mk uu____2703 t.FStar_Syntax_Syntax.pos
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
                        (fun env1  -> fun uu____2766  -> dummy :: env1) env
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
                    let uu____2787 =
                      let uu____2798 = FStar_Syntax_Syntax.is_top_level [lb]
                         in
                      if uu____2798
                      then ((lb.FStar_Syntax_Syntax.lbname), body)
                      else
                        (let x =
                           FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                         let uu____2820 =
                           non_tail_inline_closure_env cfg (dummy :: env0)
                             body
                            in
                         ((FStar_Util.Inl
                             (let uu___359_2836 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___359_2836.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___359_2836.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2820))
                       in
                    (match uu____2787 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___364_2854 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___364_2854.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___364_2854.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___364_2854.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___364_2854.FStar_Syntax_Syntax.lbpos)
                           }  in
                         let t1 =
                           mk
                             (FStar_Syntax_Syntax.Tm_let
                                ((false, [lb1]), body1))
                             t.FStar_Syntax_Syntax.pos
                            in
                         rebuild_closure cfg env0 stack t1)
                | FStar_Syntax_Syntax.Tm_let ((uu____2871,lbs),body) ->
                    let norm_one_lb env1 lb =
                      let env_univs =
                        FStar_List.fold_right
                          (fun uu____2937  -> fun env2  -> dummy :: env2)
                          lb.FStar_Syntax_Syntax.lbunivs env1
                         in
                      let env2 =
                        let uu____2954 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2954
                        then env_univs
                        else
                          FStar_List.fold_right
                            (fun uu____2969  -> fun env2  -> dummy :: env2)
                            lbs env_univs
                         in
                      let ty =
                        non_tail_inline_closure_env cfg env_univs
                          lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let nm =
                        let uu____2993 = FStar_Syntax_Syntax.is_top_level lbs
                           in
                        if uu____2993
                        then lb.FStar_Syntax_Syntax.lbname
                        else
                          (let x =
                             FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Util.Inl
                             (let uu___387_3004 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___387_3004.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___387_3004.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___390_3005 = lb  in
                      let uu____3006 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___390_3005.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___390_3005.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____3006;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___390_3005.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___390_3005.FStar_Syntax_Syntax.lbpos)
                      }  in
                    let lbs1 =
                      FStar_All.pipe_right lbs
                        (FStar_List.map (norm_one_lb env))
                       in
                    let body1 =
                      let body_env =
                        FStar_List.fold_right
                          (fun uu____3038  -> fun env1  -> dummy :: env1)
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
            (fun uu____3130  ->
               let uu____3131 = FStar_Syntax_Print.tag_of_term t  in
               let uu____3133 = env_to_string env  in
               let uu____3135 = stack_to_string stack  in
               let uu____3137 = FStar_Syntax_Print.term_to_string t  in
               FStar_Util.print4
                 "\n>>> %s (env=%s, stack=%s) Rebuild closure_as_term %s\n"
                 uu____3131 uu____3133 uu____3135 uu____3137);
          (match stack with
           | [] -> t
           | (Arg (Clos (env_arg,tm,uu____3144,uu____3145),aq,r))::stack1 ->
               let stack2 = (App (env, t, aq, r)) :: stack1  in
               inline_closure_env cfg env_arg stack2 tm
           | (App (env1,head1,aq,r))::stack1 ->
               let t1 =
                 FStar_Syntax_Syntax.extend_app head1 (t, aq)
                   FStar_Pervasives_Native.None r
                  in
               rebuild_closure cfg env1 stack1 t1
           | (Abs (env',bs,env'',lopt,r))::stack1 ->
               let uu____3226 = close_binders cfg env' bs  in
               (match uu____3226 with
                | (bs1,uu____3242) ->
                    let lopt1 = close_lcomp_opt cfg env'' lopt  in
                    let uu____3262 =
                      let uu___448_3265 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___448_3265.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___448_3265.FStar_Syntax_Syntax.vars)
                      }  in
                    rebuild_closure cfg env stack1 uu____3262)
           | (Match (env1,branches,cfg1,r))::stack1 ->
               let close_one_branch env2 uu____3321 =
                 match uu____3321 with
                 | (pat,w_opt,tm) ->
                     let rec norm_pat env3 p =
                       match p.FStar_Syntax_Syntax.v with
                       | FStar_Syntax_Syntax.Pat_constant uu____3436 ->
                           (p, env3)
                       | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                           let uu____3467 =
                             FStar_All.pipe_right pats
                               (FStar_List.fold_left
                                  (fun uu____3556  ->
                                     fun uu____3557  ->
                                       match (uu____3556, uu____3557) with
                                       | ((pats1,env4),(p1,b)) ->
                                           let uu____3707 = norm_pat env4 p1
                                              in
                                           (match uu____3707 with
                                            | (p2,env5) ->
                                                (((p2, b) :: pats1), env5)))
                                  ([], env3))
                              in
                           (match uu____3467 with
                            | (pats1,env4) ->
                                ((let uu___485_3877 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___485_3877.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___489_3898 = x  in
                             let uu____3899 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___489_3898.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___489_3898.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3899
                             }  in
                           ((let uu___492_3913 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___492_3913.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___496_3924 = x  in
                             let uu____3925 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___496_3924.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___496_3924.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3925
                             }  in
                           ((let uu___499_3939 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___499_3939.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___505_3955 = x  in
                             let uu____3956 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___505_3955.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___505_3955.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3956
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___509_3973 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___509_3973.FStar_Syntax_Syntax.p)
                             }), env3)
                        in
                     let uu____3978 = norm_pat env2 pat  in
                     (match uu____3978 with
                      | (pat1,env3) ->
                          let w_opt1 =
                            match w_opt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Pervasives_Native.None
                            | FStar_Pervasives_Native.Some w ->
                                let uu____4047 =
                                  non_tail_inline_closure_env cfg1 env3 w  in
                                FStar_Pervasives_Native.Some uu____4047
                             in
                          let tm1 = non_tail_inline_closure_env cfg1 env3 tm
                             in
                          (pat1, w_opt1, tm1))
                  in
               let t1 =
                 let uu____4066 =
                   let uu____4067 =
                     let uu____4090 =
                       FStar_All.pipe_right branches
                         (FStar_List.map (close_one_branch env1))
                        in
                     (t, uu____4090)  in
                   FStar_Syntax_Syntax.Tm_match uu____4067  in
                 mk uu____4066 t.FStar_Syntax_Syntax.pos  in
               rebuild_closure cfg1 env1 stack1 t1
           | (Meta (env_m,m,r))::stack1 ->
               let m1 =
                 match m with
                 | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
                     let uu____4226 =
                       let uu____4247 =
                         FStar_All.pipe_right names1
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m))
                          in
                       let uu____4264 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1  ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4373  ->
                                         match uu____4373 with
                                         | (a,q) ->
                                             let uu____4400 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a
                                                in
                                             (uu____4400, q)))))
                          in
                       (uu____4247, uu____4264)  in
                     FStar_Syntax_Syntax.Meta_pattern uu____4226
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4429 =
                       let uu____4436 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4436)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4429
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4448 =
                       let uu____4457 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4457)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4448
                 | uu____4462 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____4468 -> failwith "Impossible: unexpected stack element")

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
            let uu____4484 =
              let uu____4485 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____4485  in
            FStar_Pervasives_Native.Some uu____4484
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
        let uu____4502 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4586  ->
                  fun uu____4587  ->
                    match (uu____4586, uu____4587) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___564_4727 = b  in
                          let uu____4728 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___564_4727.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___564_4727.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4728
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____4502 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4870 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4883 = inline_closure_env cfg env [] t  in
                 let uu____4884 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4883 uu____4884
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4897 = inline_closure_env cfg env [] t  in
                 let uu____4898 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4897 uu____4898
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____4952  ->
                           match uu____4952 with
                           | (a,q) ->
                               let uu____4973 =
                                 inline_closure_env cfg env [] a  in
                               (uu____4973, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_4990  ->
                           match uu___5_4990 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____4994 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____4994
                           | f -> f))
                    in
                 let uu____4998 =
                   let uu___597_4999 = c1  in
                   let uu____5000 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5000;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___597_4999.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____4998)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___6_5010  ->
            match uu___6_5010 with
            | FStar_Syntax_Syntax.DECREASES uu____5012 -> false
            | uu____5016 -> true))

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
                   (fun uu___7_5035  ->
                      match uu___7_5035 with
                      | FStar_Syntax_Syntax.DECREASES uu____5037 -> false
                      | uu____5041 -> true))
               in
            let rc1 =
              let uu___614_5044 = rc  in
              let uu____5045 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___614_5044.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5045;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5054 -> lopt

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
    let uu____5102 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____5102 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5141 = FStar_Syntax_Embeddings.unembed e t  in
        uu____5141 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____5161 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____5161) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____5223  ->
           fun subst1  ->
             match uu____5223 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____5264,uu____5265)) ->
                      let uu____5326 = b  in
                      (match uu____5326 with
                       | (bv,uu____5334) ->
                           let uu____5335 =
                             let uu____5337 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5337  in
                           if uu____5335
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____5345 = unembed_binder term1  in
                              match uu____5345 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5352 =
                                      let uu___649_5353 = bv  in
                                      let uu____5354 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___649_5353.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___649_5353.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5354
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5352
                                     in
                                  let b_for_x =
                                    let uu____5360 =
                                      let uu____5367 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5367)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5360  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___8_5383  ->
                                         match uu___8_5383 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5385,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5387;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5388;_})
                                             ->
                                             let uu____5393 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5393
                                         | uu____5395 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____5397 -> subst1)) env []
  
let reduce_primops :
  'Auu____5419 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5419)
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
            (let uu____5471 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5471 with
             | (head1,args) ->
                 let uu____5516 =
                   let uu____5517 = FStar_Syntax_Util.un_uinst head1  in
                   uu____5517.FStar_Syntax_Syntax.n  in
                 (match uu____5516 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5523 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5523 with
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
                                (fun uu____5546  ->
                                   let uu____5547 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5549 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5551 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5547 uu____5549 uu____5551);
                              tm)
                           else
                             (let uu____5556 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5556 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5642  ->
                                        let uu____5643 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5643);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5648  ->
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
                                           (fun uu____5662  ->
                                              let uu____5663 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5663);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5671  ->
                                              let uu____5672 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5674 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5672 uu____5674);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5677 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5681  ->
                                 let uu____5682 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5682);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5688  ->
                            let uu____5689 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5689);
                       (match args with
                        | (a1,uu____5695)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5720 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5734  ->
                            let uu____5735 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5735);
                       (match args with
                        | (t,uu____5741)::(r,uu____5743)::[] ->
                            let uu____5784 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5784 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5790 -> tm))
                  | uu____5801 -> tm))
  
let reduce_equality :
  'Auu____5812 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5812)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___737_5861 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___739_5864 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___739_5864.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___739_5864.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___739_5864.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___739_5864.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___739_5864.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___739_5864.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___739_5864.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___739_5864.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___739_5864.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___739_5864.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___739_5864.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___739_5864.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___739_5864.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___739_5864.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___739_5864.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___739_5864.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___739_5864.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___739_5864.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___739_5864.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___737_5861.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___737_5861.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___737_5861.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___737_5861.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___737_5861.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___737_5861.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___737_5861.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____5875 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____5886 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____5897 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____5918 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____5918
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____5950 =
        let uu____5951 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5951.FStar_Syntax_Syntax.n  in
      match uu____5950 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.of_int (2))
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux Prims.int_one
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.of_int (3))
      | uu____5960 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____5969 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____5969)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____5982 =
        let uu____5983 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5983.FStar_Syntax_Syntax.n  in
      match uu____5982 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6041 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____6041 rest
           | uu____6068 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > Prims.int_zero ->
               let uu____6108 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____6108 rest
           | uu____6127 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when (FStar_List.length rest) > Prims.int_zero
               ->
               let uu____6201 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____6201 rest
           | uu____6236 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6238 ->
          let uu____6239 =
            let uu____6241 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6241
             in
          failwith uu____6239
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6262  ->
    match uu___9_6262 with
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
        let uu____6269 =
          let uu____6272 =
            let uu____6273 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6273  in
          [uu____6272]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6269
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____6281 =
          let uu____6284 =
            let uu____6285 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____6285  in
          [uu____6284]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6281
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____6293 =
          let uu____6296 =
            let uu____6297 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6297  in
          [uu____6296]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6293
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____6322 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____6322) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6373 =
            let uu____6378 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6378 s  in
          match uu____6373 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6394 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6394
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
        | uu____6429::(tm,uu____6431)::[] ->
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
        | (tm,uu____6460)::[] ->
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
        | (steps,uu____6481)::uu____6482::(tm,uu____6484)::[] ->
            let add_exclude s z =
              let uu____6522 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____6522
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____6529 =
              let uu____6534 = full_norm steps  in parse_steps uu____6534  in
            (match uu____6529 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____6573 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6605 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6612  ->
                    match uu___10_6612 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6614 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6616 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6620 -> true
                    | uu____6624 -> false))
             in
          if uu____6605
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6634  ->
             let uu____6635 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6635);
        (let tm_norm =
           let uu____6639 =
             let uu____6654 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6654.FStar_TypeChecker_Env.nbe  in
           uu____6639 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6658  ->
              let uu____6659 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6659);
         tm_norm)
  
let firstn :
  'Auu____6669 .
    Prims.int ->
      'Auu____6669 Prims.list ->
        ('Auu____6669 Prims.list * 'Auu____6669 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___11_6726 =
        match uu___11_6726 with
        | (MemoLazy uu____6731)::s -> drop_irrel s
        | (UnivArgs uu____6741)::s -> drop_irrel s
        | s -> s  in
      let uu____6754 = drop_irrel stack  in
      match uu____6754 with
      | (App
          (uu____6758,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6759;
                        FStar_Syntax_Syntax.vars = uu____6760;_},uu____6761,uu____6762))::uu____6763
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6768 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6797) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6807) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6828  ->
                  match uu____6828 with
                  | (a,uu____6839) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6850 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6875 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6877 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6891 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6893 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6895 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6897 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6899 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6902 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6910 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6918 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6933 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6953 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6969 -> true
    | FStar_Syntax_Syntax.Tm_match uu____6977 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7049  ->
                   match uu____7049 with
                   | (a,uu____7060) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7071) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____7170,args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7225  ->
                        match uu____7225 with
                        | (a,uu____7236) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7245,uu____7246,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7252,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7258 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7268 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7270 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7281 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7292 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7303 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7314 -> false
  
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
            let uu____7347 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7347 with
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
              (fun uu____7546  ->
                 fun uu____7547  ->
                   match (uu____7546, uu____7547) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7653 =
            match uu____7653 with
            | (x,y,z) ->
                let uu____7673 = FStar_Util.string_of_bool x  in
                let uu____7675 = FStar_Util.string_of_bool y  in
                let uu____7677 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7673 uu____7675
                  uu____7677
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7705  ->
                    let uu____7706 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7708 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7706 uu____7708);
               if b then reif else no)
            else
              if
                (let uu____7723 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7723)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7728  ->
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
                          ((is_rec,uu____7763),uu____7764);
                        FStar_Syntax_Syntax.sigrng = uu____7765;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7767;
                        FStar_Syntax_Syntax.sigattrs = uu____7768;_},uu____7769),uu____7770),uu____7771,uu____7772,uu____7773)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7880  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7882,uu____7883,uu____7884,uu____7885) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7952  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7955),uu____7956);
                        FStar_Syntax_Syntax.sigrng = uu____7957;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7959;
                        FStar_Syntax_Syntax.sigattrs = uu____7960;_},uu____7961),uu____7962),uu____7963,uu____7964,uu____7965)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8072  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8074,FStar_Pervasives_Native.Some
                    uu____8075,uu____8076,uu____8077) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8145  ->
                           let uu____8146 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8146);
                      (let uu____8149 =
                         let uu____8161 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8187 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8187
                            in
                         let uu____8199 =
                           let uu____8211 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8237 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8237
                              in
                           let uu____8253 =
                             let uu____8265 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8291 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8291
                                in
                             [uu____8265]  in
                           uu____8211 :: uu____8253  in
                         uu____8161 :: uu____8199  in
                       comb_or uu____8149))
                 | (uu____8339,uu____8340,FStar_Pervasives_Native.Some
                    uu____8341,uu____8342) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8410  ->
                           let uu____8411 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8411);
                      (let uu____8414 =
                         let uu____8426 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8452 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8452
                            in
                         let uu____8464 =
                           let uu____8476 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8502 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8502
                              in
                           let uu____8518 =
                             let uu____8530 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8556 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8556
                                in
                             [uu____8530]  in
                           uu____8476 :: uu____8518  in
                         uu____8426 :: uu____8464  in
                       comb_or uu____8414))
                 | (uu____8604,uu____8605,uu____8606,FStar_Pervasives_Native.Some
                    uu____8607) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8675  ->
                           let uu____8676 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8676);
                      (let uu____8679 =
                         let uu____8691 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8717 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8717
                            in
                         let uu____8729 =
                           let uu____8741 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8767 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8767
                              in
                           let uu____8783 =
                             let uu____8795 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8821 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8821
                                in
                             [uu____8795]  in
                           uu____8741 :: uu____8783  in
                         uu____8691 :: uu____8729  in
                       comb_or uu____8679))
                 | uu____8869 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8915  ->
                           let uu____8916 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____8918 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____8920 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____8916 uu____8918 uu____8920);
                      (let uu____8923 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_8929  ->
                                 match uu___12_8929 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____8935 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____8935 l))
                          in
                       FStar_All.pipe_left yesno uu____8923)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____8951  ->
               let uu____8952 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____8954 =
                 let uu____8956 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____8956  in
               let uu____8957 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____8952 uu____8954 uu____8957);
          (match res with
           | (false ,uu____8960,uu____8961) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____8986 ->
               let uu____8996 =
                 let uu____8998 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____8998
                  in
               FStar_All.pipe_left failwith uu____8996)
  
let decide_unfolding :
  'Auu____9017 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____9017 ->
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
                    let uu___1144_9086 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1146_9089 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1146_9089.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1146_9089.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1144_9086.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____9151 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____9151
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9163 =
                      let uu____9170 =
                        let uu____9171 =
                          let uu____9172 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____9172  in
                        FStar_Syntax_Syntax.Tm_constant uu____9171  in
                      FStar_Syntax_Syntax.mk uu____9170  in
                    uu____9163 FStar_Pervasives_Native.None
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
    let uu____9238 =
      let uu____9239 = FStar_Syntax_Subst.compress t  in
      uu____9239.FStar_Syntax_Syntax.n  in
    match uu____9238 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9270 =
          let uu____9271 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9271.FStar_Syntax_Syntax.n  in
        (match uu____9270 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9288 =
                 let uu____9295 =
                   let uu____9306 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9306 FStar_List.tl  in
                 FStar_All.pipe_right uu____9295 FStar_List.hd  in
               FStar_All.pipe_right uu____9288 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9405 -> FStar_Pervasives_Native.None)
    | uu____9406 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9685 ->
                   let uu____9708 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9708
               | uu____9711 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9721  ->
               let uu____9722 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9724 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9726 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9728 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9736 =
                 let uu____9738 =
                   let uu____9741 = firstn (Prims.of_int (4)) stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9741
                    in
                 stack_to_string uu____9738  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9722 uu____9724 uu____9726 uu____9728 uu____9736);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9769  ->
               let uu____9770 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9770);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9776  ->
                     let uu____9777 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9777);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9780 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9784  ->
                     let uu____9785 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9785);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____9788 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9792  ->
                     let uu____9793 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9793);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9796 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9800  ->
                     let uu____9801 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9801);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9804;
                 FStar_Syntax_Syntax.fv_delta = uu____9805;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9809  ->
                     let uu____9810 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9810);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9813;
                 FStar_Syntax_Syntax.fv_delta = uu____9814;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9815);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9825  ->
                     let uu____9826 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9826);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____9832 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____9832 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _9835) when
                    _9835 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9839  ->
                          let uu____9840 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9840);
                     rebuild cfg env stack t1)
                | uu____9843 ->
                    let uu____9846 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____9846 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____9873 ->
               let uu____9880 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____9880
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9908 = is_norm_request hd1 args  in
                  uu____9908 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____9914 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____9914))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9942 = is_norm_request hd1 args  in
                  uu____9942 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1253_9949 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1255_9952 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1255_9952.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1253_9949.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1253_9949.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1253_9949.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1253_9949.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1253_9949.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1253_9949.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____9959 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____9959 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____9995  ->
                                 fun stack1  ->
                                   match uu____9995 with
                                   | (a,aq) ->
                                       let uu____10007 =
                                         let uu____10008 =
                                           let uu____10015 =
                                             let uu____10016 =
                                               let uu____10048 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____10048, false)
                                                in
                                             Clos uu____10016  in
                                           (uu____10015, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10008  in
                                       uu____10007 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10116  ->
                            let uu____10117 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10117);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10144 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____10144)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____10155 =
                            let uu____10157 =
                              let uu____10159 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____10159  in
                            FStar_Util.string_of_int uu____10157  in
                          let uu____10166 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____10168 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____10155 uu____10166 uu____10168)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10187 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____10187)
                      else ();
                      (let delta_level =
                         let uu____10195 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___13_10202  ->
                                   match uu___13_10202 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____10204 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____10206 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____10210 -> true
                                   | uu____10214 -> false))
                            in
                         if uu____10195
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1296_10222 = cfg  in
                         let uu____10223 =
                           let uu___1298_10224 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1298_10224.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____10223;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1296_10222.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1296_10222.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1296_10222.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1296_10222.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1296_10222.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1296_10222.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____10232 =
                             let uu____10233 =
                               let uu____10238 = FStar_Util.now ()  in
                               (t1, uu____10238)  in
                             Debug uu____10233  in
                           uu____10232 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10243 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10243
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10254 =
                      let uu____10261 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10261, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10254  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10270 = lookup_bvar env x  in
               (match uu____10270 with
                | Univ uu____10271 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____10325 = FStar_ST.op_Bang r  in
                      (match uu____10325 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10421  ->
                                 let uu____10422 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10424 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10422
                                   uu____10424);
                            (let uu____10427 = maybe_weakly_reduced t'  in
                             if uu____10427
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____10430 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10474)::uu____10475 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10486,uu____10487))::stack_rest ->
                    (match c with
                     | Univ uu____10491 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10500 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10530  ->
                                    let uu____10531 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10531);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10567  ->
                                    let uu____10568 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10568);
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
                       (fun uu____10616  ->
                          let uu____10617 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10617);
                     norm cfg env stack1 t1)
                | (Match uu____10620)::uu____10621 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10636 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10636 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10672  -> dummy :: env1) env)
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
                                          let uu____10716 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10716)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1416_10724 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1416_10724.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1416_10724.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10725 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10731  ->
                                 let uu____10732 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10732);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1423_10747 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1423_10747.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1423_10747.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1423_10747.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1423_10747.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1423_10747.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1423_10747.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1423_10747.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1423_10747.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____10751)::uu____10752 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10763 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10763 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10799  -> dummy :: env1) env)
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
                                          let uu____10843 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10843)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1416_10851 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1416_10851.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1416_10851.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10852 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10858  ->
                                 let uu____10859 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10859);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1423_10874 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1423_10874.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1423_10874.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1423_10874.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1423_10874.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1423_10874.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1423_10874.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1423_10874.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1423_10874.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10878)::uu____10879 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10892 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10892 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10928  -> dummy :: env1) env)
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
                                          let uu____10972 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10972)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1416_10980 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1416_10980.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1416_10980.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10981 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10987  ->
                                 let uu____10988 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10988);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1423_11003 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1423_11003.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1423_11003.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1423_11003.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1423_11003.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1423_11003.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1423_11003.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1423_11003.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1423_11003.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11007)::uu____11008 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11023 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11023 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11059  -> dummy :: env1) env)
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
                                          let uu____11103 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11103)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1416_11111 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1416_11111.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1416_11111.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11112 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11118  ->
                                 let uu____11119 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11119);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1423_11134 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1423_11134.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1423_11134.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1423_11134.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1423_11134.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1423_11134.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1423_11134.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1423_11134.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1423_11134.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11138)::uu____11139 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11154 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11154 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11190  -> dummy :: env1) env)
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
                                          let uu____11234 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11234)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1416_11242 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1416_11242.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1416_11242.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11243 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11249  ->
                                 let uu____11250 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11250);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1423_11265 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1423_11265.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1423_11265.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1423_11265.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1423_11265.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1423_11265.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1423_11265.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1423_11265.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1423_11265.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11269)::uu____11270 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11289 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11289 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11325  -> dummy :: env1) env)
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
                                          let uu____11369 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11369)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1416_11377 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1416_11377.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1416_11377.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11378 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11384  ->
                                 let uu____11385 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11385);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1423_11400 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1423_11400.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1423_11400.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1423_11400.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1423_11400.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1423_11400.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1423_11400.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1423_11400.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1423_11400.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____11408 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11408 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11444  -> dummy :: env1) env)
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
                                          let uu____11488 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11488)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1416_11496 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1416_11496.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1416_11496.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11497 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11503  ->
                                 let uu____11504 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11504);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1423_11519 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1423_11519.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1423_11519.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1423_11519.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1423_11519.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1423_11519.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1423_11519.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1423_11519.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1423_11519.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let strict_args =
                 let uu____11555 =
                   let uu____11556 = FStar_Syntax_Util.un_uinst head1  in
                   uu____11556.FStar_Syntax_Syntax.n  in
                 match uu____11555 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11565 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11586  ->
                              fun stack1  ->
                                match uu____11586 with
                                | (a,aq) ->
                                    let uu____11598 =
                                      let uu____11599 =
                                        let uu____11606 =
                                          let uu____11607 =
                                            let uu____11639 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11639, false)  in
                                          Clos uu____11607  in
                                        (uu____11606, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11599  in
                                    uu____11598 :: stack1) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11707  ->
                          let uu____11708 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11708);
                     norm cfg env stack1 head1)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____11759  ->
                              match uu____11759 with
                              | (a,i) ->
                                  let uu____11770 = norm cfg env [] a  in
                                  (uu____11770, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____11776 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____11791 = FStar_List.nth norm_args i
                                    in
                                 match uu____11791 with
                                 | (arg_i,uu____11802) ->
                                     let uu____11803 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____11803 with
                                      | (head2,uu____11822) ->
                                          let uu____11847 =
                                            let uu____11848 =
                                              FStar_Syntax_Util.un_uinst
                                                head2
                                               in
                                            uu____11848.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____11847 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____11852 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____11855 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____11855
                                           | uu____11856 -> false)))))
                       in
                    if uu____11776
                    then
                      let stack1 =
                        FStar_All.pipe_right stack
                          (FStar_List.fold_right
                             (fun uu____11873  ->
                                fun stack1  ->
                                  match uu____11873 with
                                  | (a,aq) ->
                                      let uu____11885 =
                                        let uu____11886 =
                                          let uu____11893 =
                                            let uu____11894 =
                                              let uu____11926 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env, a, uu____11926, false)
                                               in
                                            Clos uu____11894  in
                                          (uu____11893, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____11886  in
                                      uu____11885 :: stack1) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12008  ->
                            let uu____12009 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12009);
                       norm cfg env stack1 head1)
                    else
                      (let head2 = closure_as_term cfg env head1  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                           FStar_Pervasives_Native.None
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env stack term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12029) when
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
                             ((let uu___1485_12074 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1485_12074.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1485_12074.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12075 ->
                      let uu____12090 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12090)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12094 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12094 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12125 =
                          let uu____12126 =
                            let uu____12133 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1494_12139 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1494_12139.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1494_12139.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12133)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12126  in
                        mk uu____12125 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12163 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12163
               else
                 (let uu____12166 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12166 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12174 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12200  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12174 c1  in
                      let t2 =
                        let uu____12224 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12224 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12337)::uu____12338 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12351  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12353)::uu____12354 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12365  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12367,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12368;
                                   FStar_Syntax_Syntax.vars = uu____12369;_},uu____12370,uu____12371))::uu____12372
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12379  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12381)::uu____12382 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12393  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12395 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12398  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12403  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12429 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12429
                         | FStar_Util.Inr c ->
                             let uu____12443 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12443
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12466 =
                               let uu____12467 =
                                 let uu____12494 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12494, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12467
                                in
                             mk uu____12466 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12529 ->
                           let uu____12530 =
                             let uu____12531 =
                               let uu____12532 =
                                 let uu____12559 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12559, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12532
                                in
                             mk uu____12531 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12530))))
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
                   let uu___1573_12637 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1575_12640 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1575_12640.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1573_12637.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1573_12637.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1573_12637.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1573_12637.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1573_12637.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1573_12637.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1573_12637.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1573_12637.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____12681 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12681 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1588_12701 = cfg  in
                               let uu____12702 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1588_12701.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12702;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1588_12701.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1588_12701.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1588_12701.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1588_12701.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1588_12701.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1588_12701.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1588_12701.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____12709 =
                                 let uu____12710 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12710  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12709
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1595_12713 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1595_12713.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1595_12713.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1595_12713.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1595_12713.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12714 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12714
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12727,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12728;
                               FStar_Syntax_Syntax.lbunivs = uu____12729;
                               FStar_Syntax_Syntax.lbtyp = uu____12730;
                               FStar_Syntax_Syntax.lbeff = uu____12731;
                               FStar_Syntax_Syntax.lbdef = uu____12732;
                               FStar_Syntax_Syntax.lbattrs = uu____12733;
                               FStar_Syntax_Syntax.lbpos = uu____12734;_}::uu____12735),uu____12736)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12782 =
                 (Prims.op_Negation
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.do_not_unfold_pure_lets)
                   &&
                   ((((cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations
                        &&
                        (FStar_Syntax_Util.has_attribute
                           lb.FStar_Syntax_Syntax.lbattrs
                           FStar_Parser_Const.inline_let_attr))
                       ||
                       ((FStar_Syntax_Util.is_pure_effect n1) &&
                          (cfg.FStar_TypeChecker_Cfg.normalize_pure_lets ||
                             (FStar_Syntax_Util.has_attribute
                                lb.FStar_Syntax_Syntax.lbattrs
                                FStar_Parser_Const.inline_let_attr))))
                      ||
                      ((FStar_Syntax_Util.is_ghost_effect n1) &&
                         (Prims.op_Negation
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.pure_subterms_within_computations)))
                  in
               if uu____12782
               then
                 let binder =
                   let uu____12786 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12786  in
                 let env1 =
                   let uu____12796 =
                     let uu____12803 =
                       let uu____12804 =
                         let uu____12836 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12836,
                           false)
                          in
                       Clos uu____12804  in
                     ((FStar_Pervasives_Native.Some binder), uu____12803)  in
                   uu____12796 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____12911  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____12918  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12920 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12920))
                 else
                   (let uu____12923 =
                      let uu____12928 =
                        let uu____12929 =
                          let uu____12936 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12936
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12929]  in
                      FStar_Syntax_Subst.open_term uu____12928 body  in
                    match uu____12923 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____12963  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12972 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12972  in
                            FStar_Util.Inl
                              (let uu___1637_12988 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1637_12988.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1637_12988.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____12991  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___1642_12994 = lb  in
                             let uu____12995 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1642_12994.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1642_12994.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12995;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1642_12994.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1642_12994.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13024  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___1649_13049 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___1649_13049.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___1649_13049.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___1649_13049.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___1649_13049.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___1649_13049.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___1649_13049.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___1649_13049.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___1649_13049.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____13053  ->
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
               let uu____13074 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13074 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13110 =
                               let uu___1665_13111 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1665_13111.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1665_13111.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13110  in
                           let uu____13112 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13112 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13138 =
                                   FStar_List.map (fun uu____13154  -> dummy)
                                     lbs1
                                    in
                                 let uu____13155 =
                                   let uu____13164 =
                                     FStar_List.map
                                       (fun uu____13186  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13164 env  in
                                 FStar_List.append uu____13138 uu____13155
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13212 =
                                       let uu___1679_13213 = rc  in
                                       let uu____13214 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1679_13213.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13214;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1679_13213.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13212
                                 | uu____13223 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1684_13229 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1684_13229.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1684_13229.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1684_13229.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1684_13229.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13239 =
                        FStar_List.map (fun uu____13255  -> dummy) lbs2  in
                      FStar_List.append uu____13239 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13263 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13263 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1693_13279 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1693_13279.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1693_13279.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____13313 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13313
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13334 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13412  ->
                        match uu____13412 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1709_13537 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1709_13537.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1709_13537.FStar_Syntax_Syntax.sort)
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
               (match uu____13334 with
                | (rec_env,memos,uu____13728) ->
                    let uu____13783 =
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
                             let uu____14032 =
                               let uu____14039 =
                                 let uu____14040 =
                                   let uu____14072 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14072, false)
                                    in
                                 Clos uu____14040  in
                               (FStar_Pervasives_Native.None, uu____14039)
                                in
                             uu____14032 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14157  ->
                     let uu____14158 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14158);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14182 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14186::uu____14187 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14192) ->
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
                             | uu____14271 -> norm cfg env stack head1)
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
                                  let uu____14319 =
                                    let uu____14340 =
                                      norm_pattern_args cfg env args  in
                                    (names2, uu____14340)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14319
                              | uu____14369 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14375 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14399 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14413 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14427 =
                        let uu____14429 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14431 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14429 uu____14431
                         in
                      failwith uu____14427
                    else
                      (let uu____14436 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____14436)
                | uu____14437 -> norm cfg env stack t2))

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
              let uu____14446 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14446 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14460  ->
                        let uu____14461 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14461);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14474  ->
                        let uu____14475 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14477 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14475 uu____14477);
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
                      | (UnivArgs (us',uu____14490))::stack1 ->
                          ((let uu____14499 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14499
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14507 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14507) us'
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
                      | uu____14543 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14546 ->
                          let uu____14549 =
                            let uu____14551 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14551
                             in
                          failwith uu____14549
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
                  let uu___1821_14579 = cfg  in
                  let uu____14580 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____14580;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1821_14579.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1821_14579.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1821_14579.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1821_14579.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1821_14579.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1821_14579.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1821_14579.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____14611,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14612;
                                    FStar_Syntax_Syntax.vars = uu____14613;_},uu____14614,uu____14615))::uu____14616
                     -> ()
                 | uu____14621 ->
                     let uu____14624 =
                       let uu____14626 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14626
                        in
                     failwith uu____14624);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____14635  ->
                      let uu____14636 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____14638 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____14636
                        uu____14638);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____14642 =
                    let uu____14643 = FStar_Syntax_Subst.compress head3  in
                    uu____14643.FStar_Syntax_Syntax.n  in
                  match uu____14642 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____14664 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____14664
                         in
                      let uu____14665 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____14665 with
                       | (uu____14666,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14676 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____14687 =
                                    let uu____14688 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14688.FStar_Syntax_Syntax.n  in
                                  match uu____14687 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____14694,uu____14695))
                                      ->
                                      let uu____14704 =
                                        let uu____14705 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____14705.FStar_Syntax_Syntax.n  in
                                      (match uu____14704 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____14711,msrc,uu____14713))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____14722 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____14722
                                       | uu____14723 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____14724 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____14725 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____14725 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___1893_14730 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___1893_14730.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___1893_14730.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___1893_14730.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___1893_14730.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___1893_14730.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____14731 = FStar_List.tl stack
                                        in
                                     let uu____14732 =
                                       let uu____14733 =
                                         let uu____14740 =
                                           let uu____14741 =
                                             let uu____14755 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____14755)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____14741
                                            in
                                         FStar_Syntax_Syntax.mk uu____14740
                                          in
                                       uu____14733
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____14731 uu____14732
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____14771 =
                                       let uu____14773 = is_return body  in
                                       match uu____14773 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____14778;
                                             FStar_Syntax_Syntax.vars =
                                               uu____14779;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____14782 -> false  in
                                     if uu____14771
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
                                          let uu____14806 =
                                            let uu____14813 =
                                              let uu____14814 =
                                                let uu____14833 =
                                                  let uu____14842 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____14842]  in
                                                (uu____14833, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____14814
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____14813
                                             in
                                          uu____14806
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____14881 =
                                            let uu____14882 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____14882.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14881 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____14888::uu____14889::[])
                                              ->
                                              let uu____14894 =
                                                let uu____14901 =
                                                  let uu____14902 =
                                                    let uu____14909 =
                                                      let uu____14910 =
                                                        let uu____14911 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____14911
                                                         in
                                                      let uu____14912 =
                                                        let uu____14915 =
                                                          let uu____14916 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____14916
                                                           in
                                                        [uu____14915]  in
                                                      uu____14910 ::
                                                        uu____14912
                                                       in
                                                    (bind1, uu____14909)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____14902
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____14901
                                                 in
                                              uu____14894
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____14919 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____14934 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____14934
                                          then
                                            let uu____14947 =
                                              let uu____14956 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____14956
                                               in
                                            let uu____14957 =
                                              let uu____14968 =
                                                let uu____14977 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____14977
                                                 in
                                              [uu____14968]  in
                                            uu____14947 :: uu____14957
                                          else []  in
                                        let reified =
<<<<<<< HEAD
                                          let args =
                                            if
                                              ed.FStar_Syntax_Syntax.is_layered
                                            then
                                              let rest_bs =
                                                let uu____15073 =
                                                  let uu____15074 =
                                                    let uu____15077 =
                                                      FStar_All.pipe_right
                                                        ed.FStar_Syntax_Syntax.bind_wp
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15077
                                                      FStar_Syntax_Subst.compress
                                                     in
                                                  uu____15074.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____15073 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (uu____15100::uu____15101::bs,uu____15103)
                                                    when
                                                    (FStar_List.length bs) >=
                                                      (Prims.of_int (2))
                                                    ->
                                                    let uu____15155 =
                                                      FStar_All.pipe_right bs
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15155
                                                      FStar_Pervasives_Native.fst
                                                | uu____15261 ->
                                                    let uu____15262 =
                                                      let uu____15268 =
                                                        let uu____15270 =
                                                          FStar_Ident.string_of_lid
                                                            ed.FStar_Syntax_Syntax.mname
                                                           in
                                                        let uu____15272 =
                                                          let uu____15274 =
                                                            FStar_All.pipe_right
                                                              ed.FStar_Syntax_Syntax.bind_wp
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____15274
                                                            FStar_Syntax_Print.term_to_string
                                                           in
                                                        FStar_Util.format2
                                                          "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                          uu____15270
                                                          uu____15272
                                                         in
                                                      (FStar_Errors.Fatal_UnexpectedEffect,
                                                        uu____15268)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____15262 rng
                                                 in
                                              let uu____15298 =
                                                FStar_Syntax_Syntax.as_arg
                                                  lb.FStar_Syntax_Syntax.lbtyp
                                                 in
                                              let uu____15307 =
                                                let uu____15318 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____15327 =
                                                  let uu____15338 =
                                                    FStar_All.pipe_right
                                                      rest_bs
                                                      (FStar_List.map
                                                         (fun uu____15374  ->
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.unit_const))
                                                     in
                                                  let uu____15381 =
                                                    let uu____15392 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head4
                                                       in
                                                    let uu____15401 =
                                                      let uu____15412 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          body2
                                                         in
                                                      [uu____15412]  in
                                                    uu____15392 ::
                                                      uu____15401
                                                     in
                                                  FStar_List.append
                                                    uu____15338 uu____15381
                                                   in
                                                uu____15318 :: uu____15327
                                                 in
                                              uu____15298 :: uu____15307
                                            else
                                              (let uu____15471 =
                                                 let uu____15482 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____15491 =
                                                   let uu____15502 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   [uu____15502]  in
                                                 uu____15482 :: uu____15491
                                                  in
                                               let uu____15535 =
                                                 let uu____15546 =
                                                   let uu____15557 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       FStar_Syntax_Syntax.tun
                                                      in
                                                   let uu____15566 =
                                                     let uu____15577 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         head4
                                                        in
                                                     let uu____15586 =
                                                       let uu____15597 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let uu____15606 =
                                                         let uu____15617 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2
                                                            in
                                                         [uu____15617]  in
                                                       uu____15597 ::
                                                         uu____15606
                                                        in
                                                     uu____15577 ::
                                                       uu____15586
                                                      in
                                                   uu____15557 :: uu____15566
                                                    in
                                                 FStar_List.append
                                                   maybe_range_arg
                                                   uu____15546
                                                  in
                                               FStar_List.append uu____15471
                                                 uu____15535)
                                             in
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (bind_inst, args))
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____15698  ->
                                             let uu____15699 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____15701 =
=======
                                          let uu____15015 =
                                            let uu____15022 =
                                              let uu____15023 =
                                                let uu____15040 =
                                                  let uu____15051 =
                                                    let uu____15062 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____15071 =
                                                      let uu____15082 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____15082]  in
                                                    uu____15062 ::
                                                      uu____15071
                                                     in
                                                  let uu____15115 =
                                                    let uu____15126 =
                                                      let uu____15137 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____15146 =
                                                        let uu____15157 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____15166 =
                                                          let uu____15177 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____15186 =
                                                            let uu____15197 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____15197]  in
                                                          uu____15177 ::
                                                            uu____15186
                                                           in
                                                        uu____15157 ::
                                                          uu____15166
                                                         in
                                                      uu____15137 ::
                                                        uu____15146
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____15126
                                                     in
                                                  FStar_List.append
                                                    uu____15051 uu____15115
                                                   in
                                                (bind_inst, uu____15040)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____15023
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____15022
                                             in
                                          uu____15015
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____15278  ->
                                             let uu____15279 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____15281 =
>>>>>>> snap
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
<<<<<<< HEAD
                                               uu____15699 uu____15701);
                                        (let uu____15704 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____15704 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____15732 = FStar_Options.defensive ()  in
                        if uu____15732
                        then
                          let is_arg_impure uu____15747 =
                            match uu____15747 with
                            | (e,q) ->
                                let uu____15761 =
                                  let uu____15762 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____15762.FStar_Syntax_Syntax.n  in
                                (match uu____15761 with
=======
                                               uu____15279 uu____15281);
                                        (let uu____15284 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____15284 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____15312 = FStar_Options.defensive ()  in
                        if uu____15312
                        then
                          let is_arg_impure uu____15327 =
                            match uu____15327 with
                            | (e,q) ->
                                let uu____15341 =
                                  let uu____15342 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____15342.FStar_Syntax_Syntax.n  in
                                (match uu____15341 with
>>>>>>> snap
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
<<<<<<< HEAD
                                     let uu____15778 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____15778
                                 | uu____15780 -> false)
                             in
                          let uu____15782 =
                            let uu____15784 =
                              let uu____15795 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____15795 :: args  in
                            FStar_Util.for_some is_arg_impure uu____15784  in
                          (if uu____15782
                           then
                             let uu____15821 =
                               let uu____15827 =
                                 let uu____15829 =
=======
                                     let uu____15358 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____15358
                                 | uu____15360 -> false)
                             in
                          let uu____15362 =
                            let uu____15364 =
                              let uu____15375 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____15375 :: args  in
                            FStar_Util.for_some is_arg_impure uu____15364  in
                          (if uu____15362
                           then
                             let uu____15401 =
                               let uu____15407 =
                                 let uu____15409 =
>>>>>>> snap
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
<<<<<<< HEAD
                                   uu____15829
                                  in
                               (FStar_Errors.Warning_Defensive, uu____15827)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____15821
                           else ())
                        else ());
                       (let fallback1 uu____15842 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15846  ->
                               let uu____15847 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____15847 "");
                          (let uu____15851 = FStar_List.tl stack  in
                           let uu____15852 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____15851 uu____15852)
                           in
                        let fallback2 uu____15858 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15862  ->
                               let uu____15863 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____15863 "");
                          (let uu____15867 = FStar_List.tl stack  in
                           let uu____15868 =
=======
                                   uu____15409
                                  in
                               (FStar_Errors.Warning_Defensive, uu____15407)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____15401
                           else ())
                        else ());
                       (let fallback1 uu____15422 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15426  ->
                               let uu____15427 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____15427 "");
                          (let uu____15431 = FStar_List.tl stack  in
                           let uu____15432 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____15431 uu____15432)
                           in
                        let fallback2 uu____15438 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15442  ->
                               let uu____15443 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____15443 "");
                          (let uu____15447 = FStar_List.tl stack  in
                           let uu____15448 =
>>>>>>> snap
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
<<<<<<< HEAD
                           norm cfg env uu____15867 uu____15868)
                           in
                        let uu____15873 =
                          let uu____15874 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____15874.FStar_Syntax_Syntax.n  in
                        match uu____15873 with
=======
                           norm cfg env uu____15447 uu____15448)
                           in
                        let uu____15453 =
                          let uu____15454 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____15454.FStar_Syntax_Syntax.n  in
                        match uu____15453 with
>>>>>>> snap
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
<<<<<<< HEAD
                            let uu____15880 =
                              let uu____15882 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____15882  in
                            if uu____15880
                            then fallback1 ()
                            else
                              (let uu____15887 =
                                 let uu____15889 =
=======
                            let uu____15460 =
                              let uu____15462 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____15462  in
                            if uu____15460
                            then fallback1 ()
                            else
                              (let uu____15467 =
                                 let uu____15469 =
>>>>>>> snap
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
<<<<<<< HEAD
                                 FStar_Option.isNone uu____15889  in
                               if uu____15887
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____15906 =
                                      let uu____15911 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____15911 args
                                       in
                                    uu____15906 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____15912 = FStar_List.tl stack  in
                                  norm cfg env uu____15912 t1))
                        | uu____15913 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____15915) ->
=======
                                 FStar_Option.isNone uu____15469  in
                               if uu____15467
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____15486 =
                                      let uu____15491 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____15491 args
                                       in
                                    uu____15486 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____15492 = FStar_List.tl stack  in
                                  norm cfg env uu____15492 t1))
                        | uu____15493 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____15495) ->
>>>>>>> snap
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
<<<<<<< HEAD
                        let uu____15939 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____15939  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____15943  ->
                            let uu____15944 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____15944);
                       (let uu____15947 = FStar_List.tl stack  in
                        norm cfg env uu____15947 lifted))
=======
                        let uu____15519 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____15519  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____15523  ->
                            let uu____15524 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____15524);
                       (let uu____15527 = FStar_List.tl stack  in
                        norm cfg env uu____15527 lifted))
>>>>>>> snap
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
<<<<<<< HEAD
                             (fun uu____16068  ->
                                match uu____16068 with
                                | (pat,wopt,tm) ->
                                    let uu____16116 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16116)))
=======
                             (fun uu____15648  ->
                                match uu____15648 with
                                | (pat,wopt,tm) ->
                                    let uu____15696 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____15696)))
>>>>>>> snap
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
<<<<<<< HEAD
                      let uu____16148 = FStar_List.tl stack  in
                      norm cfg env uu____16148 tm
                  | uu____16149 -> fallback ()))
=======
                      let uu____15728 = FStar_List.tl stack  in
                      norm cfg env uu____15728 tm
                  | uu____15729 -> fallback ()))
>>>>>>> snap

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
<<<<<<< HEAD
              (fun uu____16163  ->
                 let uu____16164 = FStar_Ident.string_of_lid msrc  in
                 let uu____16166 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16168 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16164
                   uu____16166 uu____16168);
            (let uu____16171 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____16171
             then
               let ed =
                 let uu____16175 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16175  in
               let uu____16176 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____16176 with
               | (uu____16177,return_repr) ->
                   let return_inst =
                     let uu____16190 =
                       let uu____16191 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____16191.FStar_Syntax_Syntax.n  in
                     match uu____16190 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16197::[]) ->
                         let uu____16202 =
                           let uu____16209 =
                             let uu____16210 =
                               let uu____16217 =
                                 let uu____16218 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____16218]  in
                               (return_tm, uu____16217)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____16210  in
                           FStar_Syntax_Syntax.mk uu____16209  in
                         uu____16202 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16221 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let args =
                     if ed.FStar_Syntax_Syntax.is_layered
                     then
                       let rest_bs =
                         let uu____16256 =
                           let uu____16257 =
                             let uu____16260 =
                               FStar_All.pipe_right
                                 ed.FStar_Syntax_Syntax.ret_wp
                                 FStar_Pervasives_Native.snd
                                in
                             FStar_All.pipe_right uu____16260
                               FStar_Syntax_Subst.compress
                              in
                           uu____16257.FStar_Syntax_Syntax.n  in
                         match uu____16256 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             (uu____16283::bs,uu____16285) when
                             (FStar_List.length bs) >= Prims.int_one ->
                             let uu____16325 =
                               FStar_All.pipe_right bs
                                 (FStar_List.splitAt
                                    ((FStar_List.length bs) - Prims.int_one))
                                in
                             FStar_All.pipe_right uu____16325
                               FStar_Pervasives_Native.fst
                         | uu____16431 ->
                             let uu____16432 =
                               let uu____16438 =
                                 let uu____16440 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 let uu____16442 =
                                   let uu____16444 =
                                     FStar_All.pipe_right
                                       ed.FStar_Syntax_Syntax.ret_wp
                                       FStar_Pervasives_Native.snd
                                      in
                                   FStar_All.pipe_right uu____16444
                                     FStar_Syntax_Print.term_to_string
                                    in
                                 FStar_Util.format2
                                   "ret_wp for layered effect %s is not an arrow with >= 2 binders (%s)"
                                   uu____16440 uu____16442
                                  in
                               (FStar_Errors.Fatal_UnexpectedEffect,
                                 uu____16438)
                                in
                             FStar_Errors.raise_error uu____16432
                               e.FStar_Syntax_Syntax.pos
                          in
                       let uu____16468 = FStar_Syntax_Syntax.as_arg t  in
                       let uu____16477 =
                         let uu____16488 =
                           FStar_All.pipe_right rest_bs
                             (FStar_List.map
                                (fun uu____16524  ->
                                   FStar_Syntax_Syntax.as_arg
                                     FStar_Syntax_Syntax.unit_const))
                            in
                         let uu____16531 =
                           let uu____16542 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____16542]  in
                         FStar_List.append uu____16488 uu____16531  in
                       uu____16468 :: uu____16477
                     else
                       (let uu____16585 = FStar_Syntax_Syntax.as_arg t  in
                        let uu____16594 =
                          let uu____16605 = FStar_Syntax_Syntax.as_arg e  in
                          [uu____16605]  in
                        uu____16585 :: uu____16594)
                      in
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (return_inst, args))
                     FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
             else
               (let uu____16652 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____16652 with
                | FStar_Pervasives_Native.None  ->
                    let uu____16655 =
                      let uu____16657 = FStar_Ident.text_of_lid msrc  in
                      let uu____16659 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____16657 uu____16659
                       in
                    failwith uu____16655
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16662;
                      FStar_TypeChecker_Env.mtarget = uu____16663;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16664;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____16684 =
                      let uu____16686 = FStar_Ident.text_of_lid msrc  in
                      let uu____16688 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____16686 uu____16688
                       in
                    failwith uu____16684
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16691;
                      FStar_TypeChecker_Env.mtarget = uu____16692;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16693;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____16723 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____16724 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____16723 t uu____16724))
=======
              (fun uu____15743  ->
                 let uu____15744 = FStar_Ident.string_of_lid msrc  in
                 let uu____15746 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15748 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15744
                   uu____15746 uu____15748);
            (let uu____15751 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____15751
             then
               let ed =
                 let uu____15755 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15755  in
               let uu____15756 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15756 with
               | (uu____15757,return_repr) ->
                   let return_inst =
                     let uu____15770 =
                       let uu____15771 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15771.FStar_Syntax_Syntax.n  in
                     match uu____15770 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15777::[]) ->
                         let uu____15782 =
                           let uu____15789 =
                             let uu____15790 =
                               let uu____15797 =
                                 let uu____15798 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15798]  in
                               (return_tm, uu____15797)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15790  in
                           FStar_Syntax_Syntax.mk uu____15789  in
                         uu____15782 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15801 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15805 =
                     let uu____15812 =
                       let uu____15813 =
                         let uu____15830 =
                           let uu____15841 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15850 =
                             let uu____15861 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15861]  in
                           uu____15841 :: uu____15850  in
                         (return_inst, uu____15830)  in
                       FStar_Syntax_Syntax.Tm_app uu____15813  in
                     FStar_Syntax_Syntax.mk uu____15812  in
                   uu____15805 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____15908 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____15908 with
                | FStar_Pervasives_Native.None  ->
                    let uu____15911 =
                      let uu____15913 = FStar_Ident.text_of_lid msrc  in
                      let uu____15915 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15913 uu____15915
                       in
                    failwith uu____15911
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15918;
                      FStar_TypeChecker_Env.mtarget = uu____15919;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15920;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15942 =
                      let uu____15944 = FStar_Ident.text_of_lid msrc  in
                      let uu____15946 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15944 uu____15946
                       in
                    failwith uu____15942
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15949;
                      FStar_TypeChecker_Env.mtarget = uu____15950;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15951;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____15986 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____15987 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____15986 t FStar_Syntax_Syntax.tun uu____15987))
>>>>>>> snap

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
<<<<<<< HEAD
                (fun uu____16794  ->
                   match uu____16794 with
                   | (a,imp) ->
                       let uu____16813 = norm cfg env [] a  in
                       (uu____16813, imp))))
=======
                (fun uu____16057  ->
                   match uu____16057 with
                   | (a,imp) ->
                       let uu____16076 = norm cfg env [] a  in
                       (uu____16076, imp))))
>>>>>>> snap

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
<<<<<<< HEAD
          (fun uu____16823  ->
             let uu____16824 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____16826 =
=======
          (fun uu____16086  ->
             let uu____16087 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____16089 =
>>>>>>> snap
               FStar_Util.string_of_int (FStar_List.length env)  in
<<<<<<< HEAD
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____16824 uu____16826);
=======
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
<<<<<<< HEAD
               uu____16114 uu____16116);
>>>>>>> snap
=======
               uu____16087 uu____16089);
>>>>>>> snap
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
<<<<<<< HEAD
                   let uu____16852 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16855  -> FStar_Pervasives_Native.Some _16855)
                     uu____16852
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2082_16856 = comp  in
=======
                   let uu____16115 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16118  -> FStar_Pervasives_Native.Some _16118)
                     uu____16115
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2043_16119 = comp  in
>>>>>>> snap
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
<<<<<<< HEAD
                 (uu___2082_16856.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2082_16856.FStar_Syntax_Syntax.vars)
=======
                 (uu___2043_16119.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2043_16119.FStar_Syntax_Syntax.vars)
>>>>>>> snap
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
<<<<<<< HEAD
                   let uu____16878 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16881  -> FStar_Pervasives_Native.Some _16881)
                     uu____16878
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2093_16882 = comp  in
=======
                   let uu____16141 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16144  -> FStar_Pervasives_Native.Some _16144)
                     uu____16141
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2054_16145 = comp  in
>>>>>>> snap
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
<<<<<<< HEAD
                 (uu___2093_16882.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2093_16882.FStar_Syntax_Syntax.vars)
=======
                 (uu___2054_16145.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2054_16145.FStar_Syntax_Syntax.vars)
>>>>>>> snap
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
<<<<<<< HEAD
                    fun uu____16927  ->
                      match uu____16927 with
                      | (a,i) ->
                          let uu____16947 = norm cfg env [] a  in
                          (uu____16947, i))
=======
                    fun uu____16190  ->
                      match uu____16190 with
                      | (a,i) ->
                          let uu____16210 = norm cfg env [] a  in
                          (uu____16210, i))
>>>>>>> snap
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
<<<<<<< HEAD
                    (fun uu___15_16969  ->
                       match uu___15_16969 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____16973 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____16973
=======
                    (fun uu___14_16232  ->
                       match uu___14_16232 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____16236 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____16236
>>>>>>> snap
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
<<<<<<< HEAD
             let uu___2110_16981 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2112_16984 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2112_16984.FStar_Syntax_Syntax.effect_name);
=======
             let uu___2071_16244 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2073_16247 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2073_16247.FStar_Syntax_Syntax.effect_name);
>>>>>>> snap
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
<<<<<<< HEAD
                 (uu___2110_16981.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2110_16981.FStar_Syntax_Syntax.vars)
=======
                 (uu___2071_16244.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2071_16244.FStar_Syntax_Syntax.vars)
>>>>>>> snap
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
<<<<<<< HEAD
        let uu____16988 = b  in
        match uu____16988 with
        | (x,imp) ->
            let x1 =
              let uu___2120_16996 = x  in
              let uu____16997 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2120_16996.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2120_16996.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16997
=======
        let uu____16251 = b  in
        match uu____16251 with
        | (x,imp) ->
            let x1 =
              let uu___2081_16259 = x  in
              let uu____16260 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2081_16259.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2081_16259.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16260
>>>>>>> snap
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
<<<<<<< HEAD
                  let uu____17008 =
                    let uu____17009 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____17009  in
                  FStar_Pervasives_Native.Some uu____17008
=======
                  let uu____16271 =
                    let uu____16272 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____16272  in
                  FStar_Pervasives_Native.Some uu____16271
>>>>>>> snap
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
<<<<<<< HEAD
        let uu____17020 =
          FStar_List.fold_left
            (fun uu____17054  ->
               fun b  ->
                 match uu____17054 with
=======
        let uu____16283 =
          FStar_List.fold_left
            (fun uu____16317  ->
               fun b  ->
                 match uu____16317 with
>>>>>>> snap
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
<<<<<<< HEAD
        match uu____17020 with | (nbs,uu____17134) -> FStar_List.rev nbs
=======
        match uu____16283 with | (nbs,uu____16397) -> FStar_List.rev nbs
>>>>>>> snap

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
<<<<<<< HEAD
            let uu____17166 =
              let uu___2145_17167 = rc  in
              let uu____17168 =
=======
            let uu____16429 =
              let uu___2106_16430 = rc  in
              let uu____16431 =
>>>>>>> snap
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
<<<<<<< HEAD
                  (uu___2145_17167.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17168;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2145_17167.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17166
        | uu____17177 -> lopt
=======
                  (uu___2106_16430.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16431;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2106_16430.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____16429
        | uu____16440 -> lopt
>>>>>>> snap

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
<<<<<<< HEAD
            (let uu____17187 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17189 = FStar_Syntax_Print.term_to_string tm'  in
=======
            (let uu____16450 = FStar_Syntax_Print.term_to_string tm  in
             let uu____16452 = FStar_Syntax_Print.term_to_string tm'  in
>>>>>>> snap
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
<<<<<<< HEAD
                else "NOT ") uu____17187 uu____17189)
=======
                else "NOT ") uu____16450 uu____16452)
>>>>>>> snap
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
<<<<<<< HEAD
    fun uu___16_17201  ->
      match uu___16_17201 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17214 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17214 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17218 =
=======
    fun uu___15_16464  ->
      match uu___15_16464 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____16477 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____16477 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____16481 =
>>>>>>> snap
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
<<<<<<< HEAD
               FStar_Syntax_Syntax.fv_to_tm uu____17218)
=======
               FStar_Syntax_Syntax.fv_to_tm uu____16481)
>>>>>>> snap

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
<<<<<<< HEAD
            let uu____17226 = norm_cb cfg  in
            reduce_primops uu____17226 cfg env tm  in
          let uu____17231 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17231
          then tm1
          else
            (let w t =
               let uu___2173_17250 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2173_17250.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2173_17250.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17262 =
                 let uu____17263 = FStar_Syntax_Util.unmeta t  in
                 uu____17263.FStar_Syntax_Syntax.n  in
               match uu____17262 with
=======
            let uu____16489 = norm_cb cfg  in
            reduce_primops uu____16489 cfg env tm  in
          let uu____16494 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____16494
          then tm1
          else
            (let w t =
               let uu___2134_16513 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2134_16513.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2134_16513.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____16525 =
                 let uu____16526 = FStar_Syntax_Util.unmeta t  in
                 uu____16526.FStar_Syntax_Syntax.n  in
               match uu____16525 with
>>>>>>> snap
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
<<<<<<< HEAD
               | uu____17275 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17339)::args1,(bv,uu____17342)::bs1) ->
                   let uu____17396 =
                     let uu____17397 = FStar_Syntax_Subst.compress t  in
                     uu____17397.FStar_Syntax_Syntax.n  in
                   (match uu____17396 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17402 -> false)
               | ([],[]) -> true
               | (uu____17433,uu____17434) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17485 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17487 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17485
                    uu____17487)
               else ();
               (let uu____17492 = FStar_Syntax_Util.head_and_args' t  in
                match uu____17492 with
                | (hd1,args) ->
                    let uu____17531 =
                      let uu____17532 = FStar_Syntax_Subst.compress hd1  in
                      uu____17532.FStar_Syntax_Syntax.n  in
                    (match uu____17531 with
=======
               | uu____16538 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____16602)::args1,(bv,uu____16605)::bs1) ->
                   let uu____16659 =
                     let uu____16660 = FStar_Syntax_Subst.compress t  in
                     uu____16660.FStar_Syntax_Syntax.n  in
                   (match uu____16659 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16665 -> false)
               | ([],[]) -> true
               | (uu____16696,uu____16697) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____16748 = FStar_Syntax_Print.term_to_string t  in
                  let uu____16750 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____16748
                    uu____16750)
               else ();
               (let uu____16755 = FStar_Syntax_Util.head_and_args' t  in
                match uu____16755 with
                | (hd1,args) ->
                    let uu____16794 =
                      let uu____16795 = FStar_Syntax_Subst.compress hd1  in
                      uu____16795.FStar_Syntax_Syntax.n  in
                    (match uu____16794 with
>>>>>>> snap
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
<<<<<<< HEAD
                            (let uu____17540 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____17542 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____17544 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17540 uu____17542 uu____17544)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17549 -> FStar_Pervasives_Native.None))
=======
                            (let uu____16803 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____16805 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____16807 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____16803 uu____16805 uu____16807)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____16812 -> FStar_Pervasives_Native.None))
>>>>>>> snap
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
<<<<<<< HEAD
                 (let uu____17567 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17569 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17567
                    uu____17569)
               else ();
               (let uu____17574 = FStar_Syntax_Util.is_squash t  in
                match uu____17574 with
                | FStar_Pervasives_Native.Some (uu____17585,t') ->
                    is_applied bs t'
                | uu____17597 ->
                    let uu____17606 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____17606 with
                     | FStar_Pervasives_Native.Some (uu____17617,t') ->
                         is_applied bs t'
                     | uu____17629 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____17653 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17653 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17660)::(q,uu____17662)::[])) when
=======
                 (let uu____16830 = FStar_Syntax_Print.term_to_string t  in
                  let uu____16832 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____16830
                    uu____16832)
               else ();
               (let uu____16837 = FStar_Syntax_Util.is_squash t  in
                match uu____16837 with
                | FStar_Pervasives_Native.Some (uu____16848,t') ->
                    is_applied bs t'
                | uu____16860 ->
                    let uu____16869 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____16869 with
                     | FStar_Pervasives_Native.Some (uu____16880,t') ->
                         is_applied bs t'
                     | uu____16892 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____16916 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16916 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____16923)::(q,uu____16925)::[])) when
>>>>>>> snap
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
<<<<<<< HEAD
                      (let uu____17705 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____17707 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17705 uu____17707)
                    else ();
                    (let uu____17712 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____17712 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17717 =
                           let uu____17718 = FStar_Syntax_Subst.compress p
                              in
                           uu____17718.FStar_Syntax_Syntax.n  in
                         (match uu____17717 with
=======
                      (let uu____16968 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____16970 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____16968 uu____16970)
                    else ();
                    (let uu____16975 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____16975 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____16980 =
                           let uu____16981 = FStar_Syntax_Subst.compress p
                              in
                           uu____16981.FStar_Syntax_Syntax.n  in
                         (match uu____16980 with
>>>>>>> snap
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
<<<<<<< HEAD
                               (let uu____17729 =
=======
                               (let uu____16992 =
>>>>>>> snap
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
<<<<<<< HEAD
                                FStar_Pervasives_Native.Some uu____17729))
                          | uu____17732 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____17735)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____17760 =
                           let uu____17761 = FStar_Syntax_Subst.compress p1
                              in
                           uu____17761.FStar_Syntax_Syntax.n  in
                         (match uu____17760 with
=======
                                FStar_Pervasives_Native.Some uu____16992))
                          | uu____16995 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____16998)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____17023 =
                           let uu____17024 = FStar_Syntax_Subst.compress p1
                              in
                           uu____17024.FStar_Syntax_Syntax.n  in
                         (match uu____17023 with
>>>>>>> snap
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
<<<<<<< HEAD
                               (let uu____17772 =
=======
                               (let uu____17035 =
>>>>>>> snap
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
<<<<<<< HEAD
                                FStar_Pervasives_Native.Some uu____17772))
                          | uu____17775 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____17779 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____17779 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____17784 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____17784 with
=======
                                FStar_Pervasives_Native.Some uu____17035))
                          | uu____17038 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____17042 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____17042 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____17047 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____17047 with
>>>>>>> snap
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
<<<<<<< HEAD
                                     let uu____17798 =
=======
                                     let uu____17061 =
>>>>>>> snap
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
<<<<<<< HEAD
                                     FStar_Pervasives_Native.Some uu____17798))
                               | uu____17801 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____17806)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____17831 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____17831 with
=======
                                     FStar_Pervasives_Native.Some uu____17061))
                               | uu____17064 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____17069)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____17094 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____17094 with
>>>>>>> snap
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
<<<<<<< HEAD
                                     let uu____17845 =
=======
                                     let uu____17108 =
>>>>>>> snap
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
<<<<<<< HEAD
                                     FStar_Pervasives_Native.Some uu____17845))
                               | uu____17848 -> FStar_Pervasives_Native.None)
                          | uu____17851 -> FStar_Pervasives_Native.None)
                     | uu____17854 -> FStar_Pervasives_Native.None))
               | uu____17857 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____17870 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17870 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____17876)::[],uu____17877,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17897 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____17899 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____17897
                         uu____17899)
                    else ();
                    is_quantified_const bv phi')
               | uu____17904 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____17919 =
                 let uu____17920 = FStar_Syntax_Subst.compress phi  in
                 uu____17920.FStar_Syntax_Syntax.n  in
               match uu____17919 with
               | FStar_Syntax_Syntax.Tm_match (uu____17926,br::brs) ->
                   let uu____17993 = br  in
                   (match uu____17993 with
                    | (uu____18011,uu____18012,e) ->
                        let r =
                          let uu____18034 = simp_t e  in
                          match uu____18034 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18046 =
                                FStar_List.for_all
                                  (fun uu____18065  ->
                                     match uu____18065 with
                                     | (uu____18079,uu____18080,e') ->
                                         let uu____18094 = simp_t e'  in
                                         uu____18094 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18046
=======
                                     FStar_Pervasives_Native.Some uu____17108))
                               | uu____17111 -> FStar_Pervasives_Native.None)
                          | uu____17114 -> FStar_Pervasives_Native.None)
                     | uu____17117 -> FStar_Pervasives_Native.None))
               | uu____17120 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____17133 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17133 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____17139)::[],uu____17140,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17160 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____17162 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____17160
                         uu____17162)
                    else ();
                    is_quantified_const bv phi')
               | uu____17167 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____17182 =
                 let uu____17183 = FStar_Syntax_Subst.compress phi  in
                 uu____17183.FStar_Syntax_Syntax.n  in
               match uu____17182 with
               | FStar_Syntax_Syntax.Tm_match (uu____17189,br::brs) ->
                   let uu____17256 = br  in
                   (match uu____17256 with
                    | (uu____17274,uu____17275,e) ->
                        let r =
                          let uu____17297 = simp_t e  in
                          match uu____17297 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____17309 =
                                FStar_List.for_all
                                  (fun uu____17328  ->
                                     match uu____17328 with
                                     | (uu____17342,uu____17343,e') ->
                                         let uu____17357 = simp_t e'  in
                                         uu____17357 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____17309
>>>>>>> snap
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
<<<<<<< HEAD
               | uu____18110 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18120 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18120
=======
               | uu____17373 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____17383 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____17383
>>>>>>> snap
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
<<<<<<< HEAD
               let maybe_un_auto_squash_arg uu____18158 =
                 match uu____18158 with
                 | (t1,q) ->
                     let uu____18179 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18179 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18211 -> (t1, q))
                  in
               let uu____18224 = FStar_Syntax_Util.head_and_args t  in
               match uu____18224 with
=======
               let maybe_un_auto_squash_arg uu____17421 =
                 match uu____17421 with
                 | (t1,q) ->
                     let uu____17442 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____17442 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____17474 -> (t1, q))
                  in
               let uu____17487 = FStar_Syntax_Util.head_and_args t  in
               match uu____17487 with
>>>>>>> snap
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
<<<<<<< HEAD
               let uu____18304 =
                 let uu____18305 = FStar_Syntax_Util.unmeta ty  in
                 uu____18305.FStar_Syntax_Syntax.n  in
               match uu____18304 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18310) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18315,c) ->
=======
               let uu____17567 =
                 let uu____17568 = FStar_Syntax_Util.unmeta ty  in
                 uu____17568.FStar_Syntax_Syntax.n  in
               match uu____17567 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____17573) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____17578,c) ->
>>>>>>> snap
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
<<<<<<< HEAD
               | uu____18339 -> false  in
             let simplify1 arg =
               let uu____18372 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18372, arg)  in
             let uu____18387 = is_forall_const tm1  in
             match uu____18387 with
=======
               | uu____17602 -> false  in
             let simplify1 arg =
               let uu____17635 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____17635, arg)  in
             let uu____17650 = is_forall_const tm1  in
             match uu____17650 with
>>>>>>> snap
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
<<<<<<< HEAD
                    (let uu____18393 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18395 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18393
                       uu____18395)
                  else ();
                  (let uu____18400 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18400))
             | FStar_Pervasives_Native.None  ->
                 let uu____18401 =
                   let uu____18402 = FStar_Syntax_Subst.compress tm1  in
                   uu____18402.FStar_Syntax_Syntax.n  in
                 (match uu____18401 with
=======
                    (let uu____17656 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____17658 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____17656
                       uu____17658)
                  else ();
                  (let uu____17663 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____17663))
             | FStar_Pervasives_Native.None  ->
                 let uu____17664 =
                   let uu____17665 = FStar_Syntax_Subst.compress tm1  in
                   uu____17665.FStar_Syntax_Syntax.n  in
                 (match uu____17664 with
>>>>>>> snap
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
<<<<<<< HEAD
                              FStar_Syntax_Syntax.pos = uu____18406;
                              FStar_Syntax_Syntax.vars = uu____18407;_},uu____18408);
                         FStar_Syntax_Syntax.pos = uu____18409;
                         FStar_Syntax_Syntax.vars = uu____18410;_},args)
                      ->
                      let uu____18440 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18440
                      then
                        let uu____18443 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18443 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18501)::
                             (uu____18502,(arg,uu____18504))::[] ->
                             maybe_auto_squash arg
                         | (uu____18577,(arg,uu____18579))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18580)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18653)::uu____18654::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18724::(FStar_Pervasives_Native.Some (false
                                         ),uu____18725)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18795 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18813 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18813
                         then
                           let uu____18816 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18816 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18874)::uu____18875::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18945::(FStar_Pervasives_Native.Some (true
                                           ),uu____18946)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19016)::(uu____19017,(arg,uu____19019))::[]
                               -> maybe_auto_squash arg
                           | (uu____19092,(arg,uu____19094))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19095)::[]
                               -> maybe_auto_squash arg
                           | uu____19168 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19186 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19186
                            then
                              let uu____19189 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19189 with
                              | uu____19247::(FStar_Pervasives_Native.Some
                                              (true ),uu____19248)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19318)::uu____19319::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19389)::(uu____19390,(arg,uu____19392))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19465,(p,uu____19467))::(uu____19468,
                                                                (q,uu____19470))::[]
                                  ->
                                  let uu____19542 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19542
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19547 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19565 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19565
                               then
                                 let uu____19568 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19568 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19626)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19627)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19701)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19702)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19776)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19777)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19851)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19852)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19926,(arg,uu____19928))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19929)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20002)::(uu____20003,(arg,uu____20005))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20078,(arg,uu____20080))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20081)::[]
                                     ->
                                     let uu____20154 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20154
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20155)::(uu____20156,(arg,uu____20158))::[]
                                     ->
                                     let uu____20231 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20231
                                 | (uu____20232,(p,uu____20234))::(uu____20235,
                                                                   (q,uu____20237))::[]
                                     ->
                                     let uu____20309 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20309
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20314 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20332 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20332
                                  then
                                    let uu____20335 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20335 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20393)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20437)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20481 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20499 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20499
                                     then
                                       match args with
                                       | (t,uu____20503)::[] ->
                                           let uu____20528 =
                                             let uu____20529 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20529.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20528 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20532::[],body,uu____20534)
                                                ->
                                                let uu____20569 = simp_t body
                                                   in
                                                (match uu____20569 with
=======
                              FStar_Syntax_Syntax.pos = uu____17669;
                              FStar_Syntax_Syntax.vars = uu____17670;_},uu____17671);
                         FStar_Syntax_Syntax.pos = uu____17672;
                         FStar_Syntax_Syntax.vars = uu____17673;_},args)
                      ->
                      let uu____17703 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17703
                      then
                        let uu____17706 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17706 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17764)::
                             (uu____17765,(arg,uu____17767))::[] ->
                             maybe_auto_squash arg
                         | (uu____17840,(arg,uu____17842))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17843)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17916)::uu____17917::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17987::(FStar_Pervasives_Native.Some (false
                                         ),uu____17988)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18058 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18076 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18076
                         then
                           let uu____18079 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18079 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18137)::uu____18138::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18208::(FStar_Pervasives_Native.Some (true
                                           ),uu____18209)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18279)::(uu____18280,(arg,uu____18282))::[]
                               -> maybe_auto_squash arg
                           | (uu____18355,(arg,uu____18357))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18358)::[]
                               -> maybe_auto_squash arg
                           | uu____18431 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18449 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18449
                            then
                              let uu____18452 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18452 with
                              | uu____18510::(FStar_Pervasives_Native.Some
                                              (true ),uu____18511)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18581)::uu____18582::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18652)::(uu____18653,(arg,uu____18655))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18728,(p,uu____18730))::(uu____18731,
                                                                (q,uu____18733))::[]
                                  ->
                                  let uu____18805 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18805
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18810 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18828 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18828
                               then
                                 let uu____18831 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18831 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18889)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18890)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18964)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18965)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19039)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19040)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19114)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19115)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19189,(arg,uu____19191))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19192)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19265)::(uu____19266,(arg,uu____19268))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19341,(arg,uu____19343))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19344)::[]
                                     ->
                                     let uu____19417 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19417
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19418)::(uu____19419,(arg,uu____19421))::[]
                                     ->
                                     let uu____19494 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19494
                                 | (uu____19495,(p,uu____19497))::(uu____19498,
                                                                   (q,uu____19500))::[]
                                     ->
                                     let uu____19572 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19572
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19577 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19595 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19595
                                  then
                                    let uu____19598 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19598 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19656)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19700)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19744 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19762 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19762
                                     then
                                       match args with
                                       | (t,uu____19766)::[] ->
                                           let uu____19791 =
                                             let uu____19792 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19792.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19791 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19795::[],body,uu____19797)
                                                ->
                                                let uu____19832 = simp_t body
                                                   in
                                                (match uu____19832 with
>>>>>>> snap
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
<<<<<<< HEAD
                                                 | uu____20575 -> tm1)
                                            | uu____20579 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20581))::(t,uu____20583)::[]
                                           ->
                                           let uu____20623 =
                                             let uu____20624 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20624.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20623 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20627::[],body,uu____20629)
                                                ->
                                                let uu____20664 = simp_t body
                                                   in
                                                (match uu____20664 with
=======
                                                 | uu____19838 -> tm1)
                                            | uu____19842 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19844))::(t,uu____19846)::[]
                                           ->
                                           let uu____19886 =
                                             let uu____19887 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19887.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19886 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19890::[],body,uu____19892)
                                                ->
                                                let uu____19927 = simp_t body
                                                   in
                                                (match uu____19927 with
>>>>>>> snap
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
<<<<<<< HEAD
                                                 | uu____20672 -> tm1)
                                            | uu____20676 -> tm1)
                                       | uu____20677 -> tm1
                                     else
                                       (let uu____20690 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20690
                                        then
                                          match args with
                                          | (t,uu____20694)::[] ->
                                              let uu____20719 =
                                                let uu____20720 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20720.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20719 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20723::[],body,uu____20725)
                                                   ->
                                                   let uu____20760 =
                                                     simp_t body  in
                                                   (match uu____20760 with
=======
                                                 | uu____19935 -> tm1)
                                            | uu____19939 -> tm1)
                                       | uu____19940 -> tm1
                                     else
                                       (let uu____19953 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19953
                                        then
                                          match args with
                                          | (t,uu____19957)::[] ->
                                              let uu____19982 =
                                                let uu____19983 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19983.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19982 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19986::[],body,uu____19988)
                                                   ->
                                                   let uu____20023 =
                                                     simp_t body  in
                                                   (match uu____20023 with
>>>>>>> snap
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
<<<<<<< HEAD
                                                    | uu____20766 -> tm1)
                                               | uu____20770 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20772))::(t,uu____20774)::[]
                                              ->
                                              let uu____20814 =
                                                let uu____20815 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20815.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20814 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20818::[],body,uu____20820)
                                                   ->
                                                   let uu____20855 =
                                                     simp_t body  in
                                                   (match uu____20855 with
=======
                                                    | uu____20029 -> tm1)
                                               | uu____20033 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20035))::(t,uu____20037)::[]
                                              ->
                                              let uu____20077 =
                                                let uu____20078 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20078.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20077 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20081::[],body,uu____20083)
                                                   ->
                                                   let uu____20118 =
                                                     simp_t body  in
                                                   (match uu____20118 with
>>>>>>> snap
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
<<<<<<< HEAD
                                                    | uu____20863 -> tm1)
                                               | uu____20867 -> tm1)
                                          | uu____20868 -> tm1
                                        else
                                          (let uu____20881 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20881
=======
                                                    | uu____20126 -> tm1)
                                               | uu____20130 -> tm1)
                                          | uu____20131 -> tm1
                                        else
                                          (let uu____20144 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20144
>>>>>>> snap
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
<<<<<<< HEAD
                                                    uu____20884;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20885;_},uu____20886)::[]
=======
                                                    uu____20147;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20148;_},uu____20149)::[]
>>>>>>> snap
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
<<<<<<< HEAD
                                                    uu____20912;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20913;_},uu____20914)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20940 -> tm1
                                           else
                                             (let uu____20953 =
=======
                                                    uu____20175;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20176;_},uu____20177)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20203 -> tm1
                                           else
                                             (let uu____20216 =
>>>>>>> snap
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
<<<<<<< HEAD
                                              if uu____20953
=======
                                              if uu____20216
>>>>>>> snap
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
<<<<<<< HEAD
                                                  let uu____20967 =
                                                    let uu____20968 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____20968.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____20967 with
=======
                                                  let uu____20230 =
                                                    let uu____20231 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____20231.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____20230 with
>>>>>>> snap
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
<<<<<<< HEAD
                                                  | uu____20979 -> false  in
=======
                                                  | uu____20242 -> false  in
>>>>>>> snap
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
<<<<<<< HEAD
                                                     let uu____20993 =
=======
                                                     let uu____20256 =
>>>>>>> snap
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
<<<<<<< HEAD
                                                       uu____20993
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____21032 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____21032
=======
                                                       uu____20256
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____20295 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____20295
>>>>>>> snap
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
<<<<<<< HEAD
                                                      (let uu____21038 =
                                                         let uu____21039 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____21039.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____21038 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21042 ->
=======
                                                      (let uu____20301 =
                                                         let uu____20302 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____20302.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____20301 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____20305 ->
>>>>>>> snap
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
<<<<<<< HEAD
                                                           let uu____21050 =
=======
                                                           let uu____20313 =
>>>>>>> snap
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
<<<<<<< HEAD
                                                           if uu____21050
=======
                                                           if uu____20313
>>>>>>> snap
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
<<<<<<< HEAD
                                                                let uu____21059
                                                                  =
                                                                  let uu____21060
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____21060.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____21059
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____21066)
                                                                    -> hd1
                                                                | uu____21091
=======
                                                                let uu____20322
                                                                  =
                                                                  let uu____20323
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____20323.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____20322
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____20329)
                                                                    -> hd1
                                                                | uu____20354
>>>>>>> snap
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
<<<<<<< HEAD
                                                              let uu____21095
                                                                =
                                                                let uu____21106
=======
                                                              let uu____20358
                                                                =
                                                                let uu____20369
>>>>>>> snap
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
<<<<<<< HEAD
                                                                [uu____21106]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21095)
                                                       | uu____21139 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21144 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____21144 with
=======
                                                                [uu____20369]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____20358)
                                                       | uu____20402 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____20407 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____20407 with
>>>>>>> snap
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
<<<<<<< HEAD
                                                 | uu____21164 ->
                                                     let uu____21173 =
                                                       let uu____21180 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____21180 cfg env
                                                        in
                                                     uu____21173 tm1)))))))))
=======
                                                 | uu____20427 ->
                                                     let uu____20436 =
                                                       let uu____20443 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____20443 cfg env
                                                        in
                                                     uu____20436 tm1)))))))))
>>>>>>> snap
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
<<<<<<< HEAD
                         FStar_Syntax_Syntax.pos = uu____21186;
                         FStar_Syntax_Syntax.vars = uu____21187;_},args)
                      ->
                      let uu____21213 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21213
                      then
                        let uu____21216 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21216 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21274)::
                             (uu____21275,(arg,uu____21277))::[] ->
                             maybe_auto_squash arg
                         | (uu____21350,(arg,uu____21352))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21353)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21426)::uu____21427::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21497::(FStar_Pervasives_Native.Some (false
                                         ),uu____21498)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21568 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21586 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21586
                         then
                           let uu____21589 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21589 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21647)::uu____21648::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21718::(FStar_Pervasives_Native.Some (true
                                           ),uu____21719)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21789)::(uu____21790,(arg,uu____21792))::[]
                               -> maybe_auto_squash arg
                           | (uu____21865,(arg,uu____21867))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21868)::[]
                               -> maybe_auto_squash arg
                           | uu____21941 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21959 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21959
                            then
                              let uu____21962 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21962 with
                              | uu____22020::(FStar_Pervasives_Native.Some
                                              (true ),uu____22021)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22091)::uu____22092::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22162)::(uu____22163,(arg,uu____22165))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22238,(p,uu____22240))::(uu____22241,
                                                                (q,uu____22243))::[]
                                  ->
                                  let uu____22315 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22315
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22320 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22338 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22338
                               then
                                 let uu____22341 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____22341 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22399)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22400)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22474)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22475)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22549)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22550)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22624)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22625)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22699,(arg,uu____22701))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22702)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22775)::(uu____22776,(arg,uu____22778))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____22851,(arg,uu____22853))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____22854)::[]
                                     ->
                                     let uu____22927 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22927
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22928)::(uu____22929,(arg,uu____22931))::[]
                                     ->
                                     let uu____23004 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23004
                                 | (uu____23005,(p,uu____23007))::(uu____23008,
                                                                   (q,uu____23010))::[]
                                     ->
                                     let uu____23082 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23082
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23087 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23105 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23105
                                  then
                                    let uu____23108 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23108 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23166)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23210)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23254 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23272 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23272
                                     then
                                       match args with
                                       | (t,uu____23276)::[] ->
                                           let uu____23301 =
                                             let uu____23302 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23302.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23301 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23305::[],body,uu____23307)
                                                ->
                                                let uu____23342 = simp_t body
                                                   in
                                                (match uu____23342 with
=======
                         FStar_Syntax_Syntax.pos = uu____20449;
                         FStar_Syntax_Syntax.vars = uu____20450;_},args)
                      ->
                      let uu____20476 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20476
                      then
                        let uu____20479 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20479 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20537)::
                             (uu____20538,(arg,uu____20540))::[] ->
                             maybe_auto_squash arg
                         | (uu____20613,(arg,uu____20615))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20616)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20689)::uu____20690::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20760::(FStar_Pervasives_Native.Some (false
                                         ),uu____20761)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20831 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20849 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20849
                         then
                           let uu____20852 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20852 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20910)::uu____20911::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20981::(FStar_Pervasives_Native.Some (true
                                           ),uu____20982)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21052)::(uu____21053,(arg,uu____21055))::[]
                               -> maybe_auto_squash arg
                           | (uu____21128,(arg,uu____21130))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21131)::[]
                               -> maybe_auto_squash arg
                           | uu____21204 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21222 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21222
                            then
                              let uu____21225 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21225 with
                              | uu____21283::(FStar_Pervasives_Native.Some
                                              (true ),uu____21284)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21354)::uu____21355::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21425)::(uu____21426,(arg,uu____21428))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21501,(p,uu____21503))::(uu____21504,
                                                                (q,uu____21506))::[]
                                  ->
                                  let uu____21578 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21578
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21583 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21601 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21601
                               then
                                 let uu____21604 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21604 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21662)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21663)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21737)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21738)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21812)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21813)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21887)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21888)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21962,(arg,uu____21964))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21965)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22038)::(uu____22039,(arg,uu____22041))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____22114,(arg,uu____22116))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____22117)::[]
                                     ->
                                     let uu____22190 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22190
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22191)::(uu____22192,(arg,uu____22194))::[]
                                     ->
                                     let uu____22267 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22267
                                 | (uu____22268,(p,uu____22270))::(uu____22271,
                                                                   (q,uu____22273))::[]
                                     ->
                                     let uu____22345 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22345
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22350 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22368 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22368
                                  then
                                    let uu____22371 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22371 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22429)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22473)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22517 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22535 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22535
                                     then
                                       match args with
                                       | (t,uu____22539)::[] ->
                                           let uu____22564 =
                                             let uu____22565 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22565.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22564 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22568::[],body,uu____22570)
                                                ->
                                                let uu____22605 = simp_t body
                                                   in
                                                (match uu____22605 with
>>>>>>> snap
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
<<<<<<< HEAD
                                                 | uu____23348 -> tm1)
                                            | uu____23352 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23354))::(t,uu____23356)::[]
                                           ->
                                           let uu____23396 =
                                             let uu____23397 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23397.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23396 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23400::[],body,uu____23402)
                                                ->
                                                let uu____23437 = simp_t body
                                                   in
                                                (match uu____23437 with
=======
                                                 | uu____22611 -> tm1)
                                            | uu____22615 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22617))::(t,uu____22619)::[]
                                           ->
                                           let uu____22659 =
                                             let uu____22660 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22660.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22659 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22663::[],body,uu____22665)
                                                ->
                                                let uu____22700 = simp_t body
                                                   in
                                                (match uu____22700 with
>>>>>>> snap
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
<<<<<<< HEAD
                                                 | uu____23445 -> tm1)
                                            | uu____23449 -> tm1)
                                       | uu____23450 -> tm1
                                     else
                                       (let uu____23463 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____23463
                                        then
                                          match args with
                                          | (t,uu____23467)::[] ->
                                              let uu____23492 =
                                                let uu____23493 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23493.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23492 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23496::[],body,uu____23498)
                                                   ->
                                                   let uu____23533 =
                                                     simp_t body  in
                                                   (match uu____23533 with
=======
                                                 | uu____22708 -> tm1)
                                            | uu____22712 -> tm1)
                                       | uu____22713 -> tm1
                                     else
                                       (let uu____22726 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22726
                                        then
                                          match args with
                                          | (t,uu____22730)::[] ->
                                              let uu____22755 =
                                                let uu____22756 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22756.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22755 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22759::[],body,uu____22761)
                                                   ->
                                                   let uu____22796 =
                                                     simp_t body  in
                                                   (match uu____22796 with
>>>>>>> snap
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
<<<<<<< HEAD
                                                    | uu____23539 -> tm1)
                                               | uu____23543 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____23545))::(t,uu____23547)::[]
                                              ->
                                              let uu____23587 =
                                                let uu____23588 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23588.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23587 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23591::[],body,uu____23593)
                                                   ->
                                                   let uu____23628 =
                                                     simp_t body  in
                                                   (match uu____23628 with
=======
                                                    | uu____22802 -> tm1)
                                               | uu____22806 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22808))::(t,uu____22810)::[]
                                              ->
                                              let uu____22850 =
                                                let uu____22851 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22851.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22850 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22854::[],body,uu____22856)
                                                   ->
                                                   let uu____22891 =
                                                     simp_t body  in
                                                   (match uu____22891 with
>>>>>>> snap
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
<<<<<<< HEAD
                                                    | uu____23636 -> tm1)
                                               | uu____23640 -> tm1)
                                          | uu____23641 -> tm1
                                        else
                                          (let uu____23654 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____23654
=======
                                                    | uu____22899 -> tm1)
                                               | uu____22903 -> tm1)
                                          | uu____22904 -> tm1
                                        else
                                          (let uu____22917 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22917
>>>>>>> snap
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
<<<<<<< HEAD
                                                    uu____23657;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23658;_},uu____23659)::[]
=======
                                                    uu____22920;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22921;_},uu____22922)::[]
>>>>>>> snap
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
<<<<<<< HEAD
                                                    uu____23685;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23686;_},uu____23687)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____23713 -> tm1
                                           else
                                             (let uu____23726 =
=======
                                                    uu____22948;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22949;_},uu____22950)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22976 -> tm1
                                           else
                                             (let uu____22989 =
>>>>>>> snap
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
<<<<<<< HEAD
                                              if uu____23726
=======
                                              if uu____22989
>>>>>>> snap
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
<<<<<<< HEAD
                                                  let uu____23740 =
                                                    let uu____23741 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____23741.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____23740 with
=======
                                                  let uu____23003 =
                                                    let uu____23004 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____23004.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____23003 with
>>>>>>> snap
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
<<<<<<< HEAD
                                                  | uu____23752 -> false  in
=======
                                                  | uu____23015 -> false  in
>>>>>>> snap
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
<<<<<<< HEAD
                                                     let uu____23766 =
=======
                                                     let uu____23029 =
>>>>>>> snap
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
<<<<<<< HEAD
                                                       uu____23766
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____23801 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____23801
=======
                                                       uu____23029
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____23064 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____23064
>>>>>>> snap
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
<<<<<<< HEAD
                                                      (let uu____23807 =
                                                         let uu____23808 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____23808.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____23807 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____23811 ->
=======
                                                      (let uu____23070 =
                                                         let uu____23071 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____23071.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____23070 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____23074 ->
>>>>>>> snap
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
<<<<<<< HEAD
                                                           let uu____23819 =
=======
                                                           let uu____23082 =
>>>>>>> snap
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
<<<<<<< HEAD
                                                           if uu____23819
=======
                                                           if uu____23082
>>>>>>> snap
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
<<<<<<< HEAD
                                                                let uu____23828
                                                                  =
                                                                  let uu____23829
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____23829.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____23828
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____23835)
                                                                    -> hd1
                                                                | uu____23860
=======
                                                                let uu____23091
                                                                  =
                                                                  let uu____23092
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____23092.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____23091
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____23098)
                                                                    -> hd1
                                                                | uu____23123
>>>>>>> snap
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
<<<<<<< HEAD
                                                              let uu____23864
                                                                =
                                                                let uu____23875
=======
                                                              let uu____23127
                                                                =
                                                                let uu____23138
>>>>>>> snap
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
<<<<<<< HEAD
                                                                [uu____23875]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____23864)
                                                       | uu____23908 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____23913 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____23913 with
=======
                                                                [uu____23138]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____23127)
                                                       | uu____23171 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____23176 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____23176 with
>>>>>>> snap
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
<<<<<<< HEAD
                                                 | uu____23933 ->
                                                     let uu____23942 =
                                                       let uu____23949 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____23949 cfg env
                                                        in
                                                     uu____23942 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____23960 = simp_t t  in
                      (match uu____23960 with
=======
                                                 | uu____23196 ->
                                                     let uu____23205 =
                                                       let uu____23212 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____23212 cfg env
                                                        in
                                                     uu____23205 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____23223 = simp_t t  in
                      (match uu____23223 with
>>>>>>> snap
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
<<<<<<< HEAD
                  | FStar_Syntax_Syntax.Tm_match uu____23969 ->
                      let uu____23992 = is_const_match tm1  in
                      (match uu____23992 with
=======
                  | FStar_Syntax_Syntax.Tm_match uu____23232 ->
                      let uu____23255 = is_const_match tm1  in
                      (match uu____23255 with
>>>>>>> snap
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
<<<<<<< HEAD
                  | uu____24001 -> tm1))
=======
                  | uu____23264 -> tm1))
>>>>>>> snap

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
<<<<<<< HEAD
            (fun uu____24011  ->
               (let uu____24013 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24015 = FStar_Syntax_Print.term_to_string t  in
                let uu____24017 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24025 =
                  let uu____24027 =
                    let uu____24030 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24030
                     in
                  stack_to_string uu____24027  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24013 uu____24015 uu____24017 uu____24025);
               (let uu____24055 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24055
                then
                  let uu____24059 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24059 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24066 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24068 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24070 =
                          let uu____24072 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24072
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24066
                          uu____24068 uu____24070);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____24094 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____24102)::uu____24103 -> true
                | uu____24113 -> false)
              in
           if uu____24094
           then
             let uu____24116 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____24116 (norm cfg env stack)
=======
            (fun uu____23274  ->
               (let uu____23276 = FStar_Syntax_Print.tag_of_term t  in
                let uu____23278 = FStar_Syntax_Print.term_to_string t  in
                let uu____23280 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____23288 =
                  let uu____23290 =
                    let uu____23293 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____23293
                     in
                  stack_to_string uu____23290  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____23276 uu____23278 uu____23280 uu____23288);
               (let uu____23318 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____23318
                then
                  let uu____23322 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____23322 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____23329 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____23331 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____23333 =
                          let uu____23335 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____23335
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____23329
                          uu____23331 uu____23333);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____23357 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____23365)::uu____23366 -> true
                | uu____23376 -> false)
              in
           if uu____23357
           then
             let uu____23379 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____23379 (norm cfg env stack)
>>>>>>> snap
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
<<<<<<< HEAD
                      let uu____24130 =
                        let uu____24132 =
                          let uu____24134 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____24134  in
                        FStar_Util.string_of_int uu____24132  in
                      let uu____24141 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____24143 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____24130 uu____24141 uu____24143)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____24152,m,r))::stack1 ->
=======
                      let uu____23393 =
                        let uu____23395 =
                          let uu____23397 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____23397  in
                        FStar_Util.string_of_int uu____23395  in
                      let uu____23404 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____23406 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____23393 uu____23404 uu____23406)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____23415,m,r))::stack1 ->
>>>>>>> snap
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
<<<<<<< HEAD
                     (fun uu____24181  ->
                        let uu____24182 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24182);
=======
                     (fun uu____23444  ->
                        let uu____23445 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____23445);
>>>>>>> snap
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
<<<<<<< HEAD
                  let uu____24225 =
                    let uu___2802_24226 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2802_24226.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2802_24226.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____24225
              | (Arg (Univ uu____24229,uu____24230,uu____24231))::uu____24232
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____24236,uu____24237))::uu____24238 ->
=======
                  let uu____23488 =
                    let uu___2763_23489 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2763_23489.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2763_23489.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____23488
              | (Arg (Univ uu____23492,uu____23493,uu____23494))::uu____23495
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____23499,uu____23500))::uu____23501 ->
>>>>>>> snap
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
<<<<<<< HEAD
                  (Clos (env_arg,tm,uu____24254,uu____24255),aq,r))::stack1
                  when
                  let uu____24307 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24307 ->
                  let t2 =
                    let uu____24311 =
                      let uu____24316 =
                        let uu____24317 = closure_as_term cfg env_arg tm  in
                        (uu____24317, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____24316  in
                    uu____24311 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____24327),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24382  ->
                        let uu____24383 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____24383);
=======
                  (Clos (env_arg,tm,uu____23517,uu____23518),aq,r))::stack1
                  when
                  let uu____23570 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____23570 ->
                  let t2 =
                    let uu____23574 =
                      let uu____23579 =
                        let uu____23580 = closure_as_term cfg env_arg tm  in
                        (uu____23580, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____23579  in
                    uu____23574 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____23590),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____23645  ->
                        let uu____23646 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____23646);
>>>>>>> snap
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
<<<<<<< HEAD
                     (let uu____24403 = FStar_ST.op_Bang m  in
                      match uu____24403 with
=======
                     (let uu____23666 = FStar_ST.op_Bang m  in
                      match uu____23666 with
>>>>>>> snap
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
<<<<<<< HEAD
                      | FStar_Pervasives_Native.Some (uu____24491,a) ->
=======
                      | FStar_Pervasives_Native.Some (uu____23754,a) ->
>>>>>>> snap
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
<<<<<<< HEAD
                  let fallback msg uu____24547 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____24552  ->
                         let uu____24553 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____24553);
=======
                  let fallback msg uu____23810 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____23815  ->
                         let uu____23816 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____23816);
>>>>>>> snap
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
<<<<<<< HEAD
                  let uu____24563 =
                    let uu____24564 = FStar_Syntax_Subst.compress t1  in
                    uu____24564.FStar_Syntax_Syntax.n  in
                  (match uu____24563 with
=======
                  let uu____23826 =
                    let uu____23827 = FStar_Syntax_Subst.compress t1  in
                    uu____23827.FStar_Syntax_Syntax.n  in
                  (match uu____23826 with
>>>>>>> snap
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
<<<<<<< HEAD
                         let uu____24592 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____24592  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____24596  ->
                             let uu____24597 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____24597);
                        (let uu____24600 = FStar_List.tl stack  in
                         norm cfg env1 uu____24600 lifted))
=======
                         let uu____23855 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____23855  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____23859  ->
                             let uu____23860 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____23860);
                        (let uu____23863 = FStar_List.tl stack  in
                         norm cfg env1 uu____23863 lifted))
>>>>>>> snap
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
<<<<<<< HEAD
                            (FStar_Const.Const_reflect uu____24601);
                          FStar_Syntax_Syntax.pos = uu____24602;
                          FStar_Syntax_Syntax.vars = uu____24603;_},(e,uu____24605)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____24644 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____24661 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____24661 with
                        | (hd1,args) ->
                            let uu____24704 =
                              let uu____24705 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____24705.FStar_Syntax_Syntax.n  in
                            (match uu____24704 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____24709 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____24709 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____24712;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____24713;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____24714;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____24716;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____24717;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____24718;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____24719;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____24755 -> fallback " (3)" ())
                             | uu____24759 -> fallback " (4)" ()))
                   | uu____24761 -> fallback " (2)" ())
=======
                            (FStar_Const.Const_reflect uu____23864);
                          FStar_Syntax_Syntax.pos = uu____23865;
                          FStar_Syntax_Syntax.vars = uu____23866;_},(e,uu____23868)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____23907 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____23924 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____23924 with
                        | (hd1,args) ->
                            let uu____23967 =
                              let uu____23968 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____23968.FStar_Syntax_Syntax.n  in
                            (match uu____23967 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____23972 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____23972 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____23975;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____23976;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____23977;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____23979;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____23980;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____23981;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____23982;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____24018 -> fallback " (3)" ())
                             | uu____24022 -> fallback " (4)" ()))
                   | uu____24024 -> fallback " (2)" ())
>>>>>>> snap
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
<<<<<<< HEAD
                     (fun uu____24787  ->
                        let uu____24788 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____24788);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____24799 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____24804  ->
                           let uu____24805 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____24807 =
                             let uu____24809 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____24839  ->
                                       match uu____24839 with
                                       | (p,uu____24850,uu____24851) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____24809
=======
                     (fun uu____24050  ->
                        let uu____24051 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____24051);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____24062 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____24067  ->
                           let uu____24068 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____24070 =
                             let uu____24072 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____24102  ->
                                       match uu____24102 with
                                       | (p,uu____24113,uu____24114) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____24072
>>>>>>> snap
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
<<<<<<< HEAD
                             uu____24805 uu____24807);
=======
                             uu____24068 uu____24070);
>>>>>>> snap
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
<<<<<<< HEAD
                                (fun uu___17_24873  ->
                                   match uu___17_24873 with
=======
                                (fun uu___16_24136  ->
                                   match uu___16_24136 with
>>>>>>> snap
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
<<<<<<< HEAD
                                   | uu____24877 -> false))
                            in
                         let steps =
                           let uu___2970_24880 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
=======
                                   | uu____24140 -> false))
                            in
                         let steps =
                           let uu___2931_24143 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
>>>>>>> snap
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
<<<<<<< HEAD
                               (uu___2970_24880.FStar_TypeChecker_Cfg.unfold_fully);
=======
                               (uu___2931_24143.FStar_TypeChecker_Cfg.unfold_fully);
>>>>>>> snap
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
<<<<<<< HEAD
                               (uu___2970_24880.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___2970_24880.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___2973_24887 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___2973_24887.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___2973_24887.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___2973_24887.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___2973_24887.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___2973_24887.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___2973_24887.FStar_TypeChecker_Cfg.reifying)
=======
                               (uu___2931_24143.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___2931_24143.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___2934_24150 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___2934_24150.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___2934_24150.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___2934_24150.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___2934_24150.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___2934_24150.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___2934_24150.FStar_TypeChecker_Cfg.reifying)
>>>>>>> snap
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
<<<<<<< HEAD
                         | FStar_Syntax_Syntax.Pat_constant uu____24962 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____24993 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25082  ->
                                       fun uu____25083  ->
                                         match (uu____25082, uu____25083)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____25233 =
                                               norm_pat env3 p1  in
                                             (match uu____25233 with
=======
                         | FStar_Syntax_Syntax.Pat_constant uu____24225 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____24256 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____24345  ->
                                       fun uu____24346  ->
                                         match (uu____24345, uu____24346)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____24496 =
                                               norm_pat env3 p1  in
                                             (match uu____24496 with
>>>>>>> snap
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
<<<<<<< HEAD
                             (match uu____24993 with
                              | (pats1,env3) ->
                                  ((let uu___3001_25403 = p  in
=======
                             (match uu____24256 with
                              | (pats1,env3) ->
                                  ((let uu___2962_24666 = p  in
>>>>>>> snap
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
<<<<<<< HEAD
                                        (uu___3001_25403.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___3005_25424 = x  in
                               let uu____25425 =
=======
                                        (uu___2962_24666.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___2966_24687 = x  in
                               let uu____24688 =
>>>>>>> snap
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                   (uu___3005_25424.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3005_25424.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25425
                               }  in
                             ((let uu___3008_25439 = p  in
=======
                                   (uu___2966_24687.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2966_24687.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24688
                               }  in
                             ((let uu___2969_24702 = p  in
>>>>>>> snap
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
<<<<<<< HEAD
                                   (uu___3008_25439.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3012_25450 = x  in
                               let uu____25451 =
=======
                                   (uu___2969_24702.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___2973_24713 = x  in
                               let uu____24714 =
>>>>>>> snap
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                   (uu___3012_25450.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3012_25450.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25451
                               }  in
                             ((let uu___3015_25465 = p  in
=======
                                   (uu___2973_24713.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2973_24713.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24714
                               }  in
                             ((let uu___2976_24728 = p  in
>>>>>>> snap
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
<<<<<<< HEAD
                                   (uu___3015_25465.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3021_25481 = x  in
                               let uu____25482 =
=======
                                   (uu___2976_24728.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___2982_24744 = x  in
                               let uu____24745 =
>>>>>>> snap
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
<<<<<<< HEAD
                                   (uu___3021_25481.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3021_25481.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25482
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3025_25497 = p  in
=======
                                   (uu___2982_24744.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2982_24744.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24745
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___2986_24760 = p  in
>>>>>>> snap
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
<<<<<<< HEAD
                                   (uu___3025_25497.FStar_Syntax_Syntax.p)
=======
                                   (uu___2986_24760.FStar_Syntax_Syntax.p)
>>>>>>> snap
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
<<<<<<< HEAD
                         | uu____25541 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____25571 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____25571 with
                                     | (p,wopt,e) ->
                                         let uu____25591 = norm_pat env1 p
                                            in
                                         (match uu____25591 with
=======
                         | uu____24804 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____24834 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____24834 with
                                     | (p,wopt,e) ->
                                         let uu____24854 = norm_pat env1 p
                                            in
                                         (match uu____24854 with
>>>>>>> snap
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
<<<<<<< HEAD
                                                    let uu____25646 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____25646
=======
                                                    let uu____24909 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____24909
>>>>>>> snap
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
<<<<<<< HEAD
                         let uu____25663 =
=======
                         let uu____24926 =
>>>>>>> snap
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
<<<<<<< HEAD
                         if uu____25663
                         then
                           norm
                             (let uu___3044_25670 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3046_25673 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3046_25673.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3044_25670.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3044_25670.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3044_25670.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3044_25670.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3044_25670.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3044_25670.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3044_25670.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3044_25670.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____25677 =
=======
                         if uu____24926
                         then
                           norm
                             (let uu___3005_24933 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3007_24936 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3007_24936.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3005_24933.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3005_24933.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3005_24933.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3005_24933.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3005_24933.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3005_24933.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3005_24933.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3005_24933.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____24940 =
>>>>>>> snap
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
<<<<<<< HEAD
                       rebuild cfg1 env1 stack1 uu____25677)
                       in
                    let rec is_cons head1 =
                      let uu____25703 =
                        let uu____25704 = FStar_Syntax_Subst.compress head1
                           in
                        uu____25704.FStar_Syntax_Syntax.n  in
                      match uu____25703 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____25709) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____25714 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____25716;
                            FStar_Syntax_Syntax.fv_delta = uu____25717;
=======
                       rebuild cfg1 env1 stack1 uu____24940)
                       in
                    let rec is_cons head1 =
                      let uu____24966 =
                        let uu____24967 = FStar_Syntax_Subst.compress head1
                           in
                        uu____24967.FStar_Syntax_Syntax.n  in
                      match uu____24966 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____24972) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____24977 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____24979;
                            FStar_Syntax_Syntax.fv_delta = uu____24980;
>>>>>>> snap
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
<<<<<<< HEAD
                          { FStar_Syntax_Syntax.fv_name = uu____25719;
                            FStar_Syntax_Syntax.fv_delta = uu____25720;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____25721);_}
                          -> true
                      | uu____25729 -> false  in
=======
                          { FStar_Syntax_Syntax.fv_name = uu____24982;
                            FStar_Syntax_Syntax.fv_delta = uu____24983;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____24984);_}
                          -> true
                      | uu____24992 -> false  in
>>>>>>> snap
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
<<<<<<< HEAD
                      let uu____25898 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____25898 with
=======
                      let uu____25161 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____25161 with
>>>>>>> snap
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
<<<<<<< HEAD
                           | FStar_Syntax_Syntax.Pat_dot_term uu____25995 ->
=======
                           | FStar_Syntax_Syntax.Pat_dot_term uu____25258 ->
>>>>>>> snap
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
<<<<<<< HEAD
                                | uu____26037 ->
                                    let uu____26038 =
                                      let uu____26040 = is_cons head1  in
                                      Prims.op_Negation uu____26040  in
                                    FStar_Util.Inr uu____26038)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____26069 =
                                 let uu____26070 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____26070.FStar_Syntax_Syntax.n  in
                               (match uu____26069 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26089 ->
                                    let uu____26090 =
                                      let uu____26092 = is_cons head1  in
                                      Prims.op_Negation uu____26092  in
                                    FStar_Util.Inr uu____26090))
=======
                                | uu____25300 ->
                                    let uu____25301 =
                                      let uu____25303 = is_cons head1  in
                                      Prims.op_Negation uu____25303  in
                                    FStar_Util.Inr uu____25301)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____25332 =
                                 let uu____25333 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____25333.FStar_Syntax_Syntax.n  in
                               (match uu____25332 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____25352 ->
                                    let uu____25353 =
                                      let uu____25355 = is_cons head1  in
                                      Prims.op_Negation uu____25355  in
                                    FStar_Util.Inr uu____25353))
>>>>>>> snap
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
<<<<<<< HEAD
                      | ((t2,uu____26183)::rest_a,(p1,uu____26186)::rest_p)
                          ->
                          let uu____26245 = matches_pat t2 p1  in
                          (match uu____26245 with
=======
                      | ((t2,uu____25446)::rest_a,(p1,uu____25449)::rest_p)
                          ->
                          let uu____25508 = matches_pat t2 p1  in
                          (match uu____25508 with
>>>>>>> snap
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
<<<<<<< HEAD
                      | uu____26298 -> FStar_Util.Inr false
=======
                      | uu____25561 -> FStar_Util.Inr false
>>>>>>> snap
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
<<<<<<< HEAD
                          let uu____26421 = matches_pat scrutinee1 p1  in
                          (match uu____26421 with
=======
                          let uu____25684 = matches_pat scrutinee1 p1  in
                          (match uu____25684 with
>>>>>>> snap
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
<<<<<<< HEAD
                                  (fun uu____26467  ->
                                     let uu____26468 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____26470 =
                                       let uu____26472 =
                                         FStar_List.map
                                           (fun uu____26484  ->
                                              match uu____26484 with
                                              | (uu____26490,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____26472
=======
                                  (fun uu____25730  ->
                                     let uu____25731 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____25733 =
                                       let uu____25735 =
                                         FStar_List.map
                                           (fun uu____25747  ->
                                              match uu____25747 with
                                              | (uu____25753,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____25735
>>>>>>> snap
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
<<<<<<< HEAD
                                       uu____26468 uu____26470);
=======
                                       uu____25731 uu____25733);
>>>>>>> snap
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
<<<<<<< HEAD
                                        fun uu____26526  ->
                                          match uu____26526 with
                                          | (bv,t2) ->
                                              let uu____26549 =
                                                let uu____26556 =
                                                  let uu____26559 =
=======
                                        fun uu____25789  ->
                                          match uu____25789 with
                                          | (bv,t2) ->
                                              let uu____25812 =
                                                let uu____25819 =
                                                  let uu____25822 =
>>>>>>> snap
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
<<<<<<< HEAD
                                                    uu____26559
                                                   in
                                                let uu____26560 =
                                                  let uu____26561 =
                                                    let uu____26593 =
=======
                                                    uu____25822
                                                   in
                                                let uu____25823 =
                                                  let uu____25824 =
                                                    let uu____25856 =
>>>>>>> snap
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
<<<<<<< HEAD
                                                    ([], t2, uu____26593,
                                                      false)
                                                     in
                                                  Clos uu____26561  in
                                                (uu____26556, uu____26560)
                                                 in
                                              uu____26549 :: env2) env1 s
                                    in
                                 let uu____26686 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____26686)))
=======
                                                    ([], t2, uu____25856,
                                                      false)
                                                     in
                                                  Clos uu____25824  in
                                                (uu____25819, uu____25823)
                                                 in
                                              uu____25812 :: env2) env1 s
                                    in
                                 let uu____25949 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____25949)))
>>>>>>> snap
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
<<<<<<< HEAD
            (fun uu____26719  ->
               let uu____26720 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____26720);
          (let uu____26723 = is_nbe_request s  in
           if uu____26723
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____26729  ->
                   let uu____26730 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____26730);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____26736  ->
                   let uu____26737 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26737);
              (let uu____26740 =
                 FStar_Util.record_time (fun uu____26747  -> nbe_eval c s t)
                  in
               match uu____26740 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26756  ->
                         let uu____26757 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26759 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26757 uu____26759);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____26767  ->
                   let uu____26768 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____26768);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____26774  ->
                   let uu____26775 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26775);
              (let uu____26778 =
                 FStar_Util.record_time (fun uu____26785  -> norm c [] [] t)
                  in
               match uu____26778 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26800  ->
                         let uu____26801 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26803 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26801 uu____26803);
=======
            (fun uu____25982  ->
               let uu____25983 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____25983);
          (let uu____25986 = is_nbe_request s  in
           if uu____25986
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____25992  ->
                   let uu____25993 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____25993);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____25999  ->
                   let uu____26000 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26000);
              (let uu____26003 =
                 FStar_Util.record_time (fun uu____26010  -> nbe_eval c s t)
                  in
               match uu____26003 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26019  ->
                         let uu____26020 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26022 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26020 uu____26022);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____26030  ->
                   let uu____26031 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____26031);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____26037  ->
                   let uu____26038 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26038);
              (let uu____26041 =
                 FStar_Util.record_time (fun uu____26048  -> norm c [] [] t)
                  in
               match uu____26041 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26063  ->
                         let uu____26064 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26066 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26064 uu____26066);
>>>>>>> snap
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
<<<<<<< HEAD
        let uu____26822 =
          let uu____26826 =
            let uu____26828 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____26828  in
          FStar_Pervasives_Native.Some uu____26826  in
        FStar_Profiling.profile
          (fun uu____26831  -> normalize_with_primitive_steps [] s e t)
          uu____26822 "FStar.TypeChecker.Normalize"
=======
        let uu____26085 =
          let uu____26089 =
            let uu____26091 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____26091  in
          FStar_Pervasives_Native.Some uu____26089  in
        FStar_Profiling.profile
          (fun uu____26094  -> normalize_with_primitive_steps [] s e t)
          uu____26085 "FStar.TypeChecker.Normalize"
>>>>>>> snap
  
let (normalize_comp :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun t  ->
<<<<<<< HEAD
        let uu____26849 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____26849 [] t
=======
        let uu____26112 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____26112 [] t
>>>>>>> snap
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
<<<<<<< HEAD
      let uu____26867 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____26867 [] u
=======
      let uu____26130 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____26130 [] u
>>>>>>> snap
  
let (ghost_to_pure :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  ->
      let cfg =
        FStar_TypeChecker_Cfg.config
          [FStar_TypeChecker_Env.UnfoldUntil
             FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.Unascribe;
          FStar_TypeChecker_Env.ForExtraction] env
         in
      let non_info t =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____26185 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____26185  in
=======
        let uu____26183 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26183  in
>>>>>>> snap
=======
        let uu____26176 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26176  in
>>>>>>> snap
=======
        let uu____26839 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26839  in
>>>>>>> snap
=======
        let uu____26893 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26893  in
>>>>>>> commenting on the normalizer changes for reification of layered effects
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____26900 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3203_26919 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3203_26919.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3203_26919.FStar_Syntax_Syntax.vars)
=======
        let uu____26156 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26156  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____26163 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3164_26182 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3164_26182.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3164_26182.FStar_Syntax_Syntax.vars)
>>>>>>> snap
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
<<<<<<< HEAD
          let uu____26926 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____26926
          then
            let ct1 =
              let uu____26930 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____26930 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____26937 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____26937
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3213_26944 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3213_26944.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3213_26944.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3213_26944.FStar_Syntax_Syntax.effect_args);
=======
          let uu____26189 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____26189
          then
            let ct1 =
              let uu____26193 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____26193 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____26200 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____26200
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3174_26207 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3174_26207.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3174_26207.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3174_26207.FStar_Syntax_Syntax.effect_args);
>>>>>>> snap
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
<<<<<<< HEAD
                  let uu___3217_26946 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3217_26946.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3217_26946.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3217_26946.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3217_26946.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3220_26947 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3220_26947.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3220_26947.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____26950 -> c
=======
                  let uu___3178_26209 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3178_26209.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3178_26209.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3178_26209.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3178_26209.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3181_26210 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3181_26210.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3181_26210.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____26213 -> c
>>>>>>> snap
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lc  ->
      let cfg =
        FStar_TypeChecker_Cfg.config
          [FStar_TypeChecker_Env.Eager_unfolding;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.Unascribe;
          FStar_TypeChecker_Env.ForExtraction] env
         in
      let non_info t =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
        let uu____26262 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____26262  in
      let uu____26269 =
=======
        let uu____26253 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26253  in
      let uu____26260 =
>>>>>>> snap
=======
        let uu____26916 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26916  in
      let uu____26923 =
>>>>>>> snap
=======
        let uu____26970 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26970  in
      let uu____26977 =
>>>>>>> commenting on the normalizer changes for reification of layered effects
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info lc.FStar_TypeChecker_Common.res_typ)
=======
        let uu____26260 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26260  in
      let uu____26267 =
=======
        let uu____26233 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____26233  in
      let uu____26240 =
>>>>>>> snap
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
>>>>>>> snap
         in
<<<<<<< HEAD
      if uu____26977
      then
        let uu____26980 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____26980 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3231_26984 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3231_26984.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3231_26984.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3231_26984.FStar_TypeChecker_Common.comp_thunk)
            }
=======
      if uu____26240
      then
        let uu____26243 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____26243 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____26249  ->
                 let uu____26250 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____26250)
>>>>>>> snap
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
<<<<<<< HEAD
          (fun uu___3238_27003  ->
=======
          (fun uu___3197_26267  ->
>>>>>>> snap
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
<<<<<<< HEAD
        | uu___3237_27006 ->
            ((let uu____27008 =
                let uu____27014 =
                  let uu____27016 = FStar_Util.message_of_exn uu___3237_27006
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27016
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27014)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27008);
=======
        | uu___3196_26270 ->
            ((let uu____26272 =
                let uu____26278 =
                  let uu____26280 = FStar_Util.message_of_exn uu___3196_26270
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26280
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26278)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____26272);
>>>>>>> snap
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
<<<<<<< HEAD
          (fun uu___3248_27035  ->
             match () with
             | () ->
                 let uu____27036 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____27036 [] c) ()
        with
        | uu___3247_27045 ->
            ((let uu____27047 =
                let uu____27053 =
                  let uu____27055 = FStar_Util.message_of_exn uu___3247_27045
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27055
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27053)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27047);
=======
          (fun uu___3207_26299  ->
             match () with
             | () ->
                 let uu____26300 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____26300 [] c) ()
        with
        | uu___3206_26309 ->
            ((let uu____26311 =
                let uu____26317 =
                  let uu____26319 = FStar_Util.message_of_exn uu___3206_26309
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26319
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26317)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____26311);
>>>>>>> snap
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
<<<<<<< HEAD
                   let uu____27104 =
                     let uu____27105 =
                       let uu____27112 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27112)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27105  in
                   mk uu____27104 t01.FStar_Syntax_Syntax.pos
               | uu____27117 -> t2)
          | uu____27118 -> t2  in
=======
                   let uu____26368 =
                     let uu____26369 =
                       let uu____26376 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____26376)  in
                     FStar_Syntax_Syntax.Tm_refine uu____26369  in
                   mk uu____26368 t01.FStar_Syntax_Syntax.pos
               | uu____26381 -> t2)
          | uu____26382 -> t2  in
>>>>>>> snap
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
<<<<<<< HEAD
        let uu____27212 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27212 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27249 ->
                 let uu____27258 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27258 with
                  | (actuals,uu____27268,uu____27269) ->
=======
        let uu____26476 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____26476 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____26513 ->
                 let uu____26522 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____26522 with
                  | (actuals,uu____26532,uu____26533) ->
>>>>>>> snap
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
<<<<<<< HEAD
                        (let uu____27289 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27289 with
                         | (binders,args) ->
                             let uu____27300 =
=======
                        (let uu____26553 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____26553 with
                         | (binders,args) ->
                             let uu____26564 =
>>>>>>> snap
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
<<<<<<< HEAD
                             FStar_Syntax_Util.abs binders uu____27300
=======
                             FStar_Syntax_Util.abs binders uu____26564
>>>>>>> snap
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
<<<<<<< HEAD
      | uu____27315 ->
          let uu____27316 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27316 with
           | (head1,args) ->
               let uu____27359 =
                 let uu____27360 = FStar_Syntax_Subst.compress head1  in
                 uu____27360.FStar_Syntax_Syntax.n  in
               (match uu____27359 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____27381 =
                      let uu____27396 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____27396  in
                    (match uu____27381 with
=======
      | uu____26579 ->
          let uu____26580 = FStar_Syntax_Util.head_and_args t  in
          (match uu____26580 with
           | (head1,args) ->
               let uu____26623 =
                 let uu____26624 = FStar_Syntax_Subst.compress head1  in
                 uu____26624.FStar_Syntax_Syntax.n  in
               (match uu____26623 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____26645 =
                      let uu____26660 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____26660  in
                    (match uu____26645 with
>>>>>>> snap
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
<<<<<<< HEAD
                           (let uu____27436 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3318_27444 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3318_27444.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3318_27444.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3318_27444.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3318_27444.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3318_27444.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3318_27444.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3318_27444.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3318_27444.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3318_27444.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3318_27444.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3318_27444.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3318_27444.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3318_27444.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3318_27444.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3318_27444.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3318_27444.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3318_27444.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3318_27444.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3318_27444.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3318_27444.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3318_27444.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3318_27444.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3318_27444.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3318_27444.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3318_27444.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3318_27444.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3318_27444.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3318_27444.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3318_27444.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3318_27444.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3318_27444.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3318_27444.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                     (uu___3296_26740.FStar_TypeChecker_Env.synth_hook);
=======
                                     (uu___3294_26736.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3294_26736.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                     (uu___3294_26727.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3294_26727.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                     (uu___3318_27390.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3318_27390.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                                     (uu___3318_27444.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___3318_27444.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> commenting on the normalizer changes for reification of layered effects
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3318_27444.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3318_27444.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3318_27444.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3318_27444.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3318_27444.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3318_27444.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3318_27444.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                                     (uu___3294_26736.FStar_TypeChecker_Env.strict_args_tab)
=======
                                     (uu___3292_26735.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3292_26735.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                                     (uu___3294_26727.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3294_26727.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                                     (uu___3318_27390.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3318_27390.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                                     (uu___3318_27444.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3318_27444.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> commenting on the normalizer changes for reification of layered effects
                                 }) t
                               in
                            match uu____27436 with
                            | (uu____27447,ty,uu____27449) ->
                                eta_expand_with_type env t ty))
                | uu____27450 ->
                    let uu____27451 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3325_27459 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3325_27459.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3325_27459.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3325_27459.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3325_27459.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3325_27459.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3325_27459.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3325_27459.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3325_27459.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3325_27459.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3325_27459.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3325_27459.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3325_27459.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3325_27459.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3325_27459.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3325_27459.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3325_27459.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3325_27459.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3325_27459.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3325_27459.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3325_27459.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3325_27459.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3325_27459.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3325_27459.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3325_27459.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3325_27459.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3325_27459.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3325_27459.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3325_27459.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3325_27459.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3325_27459.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3325_27459.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3325_27459.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                             (uu___3303_26755.FStar_TypeChecker_Env.synth_hook);
=======
                             (uu___3301_26751.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3301_26751.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                             (uu___3301_26742.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3301_26742.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                             (uu___3325_27405.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3325_27405.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> snap
=======
                             (uu___3325_27459.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.try_solve_implicits_hook =
                             (uu___3325_27459.FStar_TypeChecker_Env.try_solve_implicits_hook);
>>>>>>> commenting on the normalizer changes for reification of layered effects
                           FStar_TypeChecker_Env.splice =
                             (uu___3325_27459.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3325_27459.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3325_27459.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3325_27459.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3325_27459.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3325_27459.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3325_27459.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
<<<<<<< HEAD
                             (uu___3301_26751.FStar_TypeChecker_Env.strict_args_tab)
=======
                             (uu___3299_26750.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3299_26750.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                             (uu___3301_26742.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3301_26742.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                             (uu___3325_27405.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3325_27405.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> snap
=======
                             (uu___3325_27459.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3325_27459.FStar_TypeChecker_Env.erasable_types_tab)
>>>>>>> commenting on the normalizer changes for reification of layered effects
                         }) t
                       in
                    (match uu____27451 with
                     | (uu____27462,ty,uu____27464) ->
=======
                           (let uu____26700 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3277_26708 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3277_26708.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3277_26708.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3277_26708.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3277_26708.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3277_26708.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3277_26708.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3277_26708.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3277_26708.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3277_26708.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3277_26708.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3277_26708.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3277_26708.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3277_26708.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3277_26708.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3277_26708.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3277_26708.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3277_26708.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3277_26708.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3277_26708.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3277_26708.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3277_26708.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3277_26708.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3277_26708.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3277_26708.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3277_26708.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3277_26708.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3277_26708.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3277_26708.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3277_26708.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3277_26708.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3277_26708.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3277_26708.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3277_26708.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3277_26708.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3277_26708.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3277_26708.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3277_26708.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3277_26708.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3277_26708.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3277_26708.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3277_26708.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3277_26708.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____26700 with
                            | (uu____26711,ty,uu____26713) ->
                                eta_expand_with_type env t ty))
                | uu____26714 ->
                    let uu____26715 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3284_26723 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3284_26723.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3284_26723.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3284_26723.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3284_26723.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3284_26723.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3284_26723.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3284_26723.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3284_26723.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3284_26723.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3284_26723.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3284_26723.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3284_26723.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3284_26723.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3284_26723.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3284_26723.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3284_26723.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3284_26723.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3284_26723.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3284_26723.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3284_26723.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3284_26723.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3284_26723.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3284_26723.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3284_26723.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3284_26723.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3284_26723.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3284_26723.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3284_26723.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3284_26723.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3284_26723.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3284_26723.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3284_26723.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3284_26723.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3284_26723.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3284_26723.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3284_26723.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3284_26723.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3284_26723.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3284_26723.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3284_26723.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3284_26723.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3284_26723.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____26715 with
                     | (uu____26726,ty,uu____26728) ->
>>>>>>> snap
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
<<<<<<< HEAD
      let uu___3337_27546 = x  in
      let uu____27547 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3337_27546.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3337_27546.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27547
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27550 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27574 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27575 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27576 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27577 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27584 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27585 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27586 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3363_27620 = rc  in
          let uu____27621 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____27630 =
=======
      let uu___3296_26810 = x  in
      let uu____26811 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3296_26810.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3296_26810.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____26811
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____26814 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____26838 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____26839 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____26840 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____26841 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____26848 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____26849 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____26850 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3322_26884 = rc  in
          let uu____26885 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____26894 =
>>>>>>> snap
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
<<<<<<< HEAD
              (uu___3363_27620.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27621;
            FStar_Syntax_Syntax.residual_flags = uu____27630
          }  in
        let uu____27633 =
          let uu____27634 =
            let uu____27653 = elim_delayed_subst_binders bs  in
            let uu____27662 = elim_delayed_subst_term t2  in
            let uu____27665 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____27653, uu____27662, uu____27665)  in
          FStar_Syntax_Syntax.Tm_abs uu____27634  in
        mk1 uu____27633
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____27702 =
          let uu____27703 =
            let uu____27718 = elim_delayed_subst_binders bs  in
            let uu____27727 = elim_delayed_subst_comp c  in
            (uu____27718, uu____27727)  in
          FStar_Syntax_Syntax.Tm_arrow uu____27703  in
        mk1 uu____27702
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____27746 =
          let uu____27747 =
            let uu____27754 = elim_bv bv  in
            let uu____27755 = elim_delayed_subst_term phi  in
            (uu____27754, uu____27755)  in
          FStar_Syntax_Syntax.Tm_refine uu____27747  in
        mk1 uu____27746
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____27786 =
          let uu____27787 =
            let uu____27804 = elim_delayed_subst_term t2  in
            let uu____27807 = elim_delayed_subst_args args  in
            (uu____27804, uu____27807)  in
          FStar_Syntax_Syntax.Tm_app uu____27787  in
        mk1 uu____27786
=======
              (uu___3322_26884.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____26885;
            FStar_Syntax_Syntax.residual_flags = uu____26894
          }  in
        let uu____26897 =
          let uu____26898 =
            let uu____26917 = elim_delayed_subst_binders bs  in
            let uu____26926 = elim_delayed_subst_term t2  in
            let uu____26929 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____26917, uu____26926, uu____26929)  in
          FStar_Syntax_Syntax.Tm_abs uu____26898  in
        mk1 uu____26897
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____26966 =
          let uu____26967 =
            let uu____26982 = elim_delayed_subst_binders bs  in
            let uu____26991 = elim_delayed_subst_comp c  in
            (uu____26982, uu____26991)  in
          FStar_Syntax_Syntax.Tm_arrow uu____26967  in
        mk1 uu____26966
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____27010 =
          let uu____27011 =
            let uu____27018 = elim_bv bv  in
            let uu____27019 = elim_delayed_subst_term phi  in
            (uu____27018, uu____27019)  in
          FStar_Syntax_Syntax.Tm_refine uu____27011  in
        mk1 uu____27010
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____27050 =
          let uu____27051 =
            let uu____27068 = elim_delayed_subst_term t2  in
            let uu____27071 = elim_delayed_subst_args args  in
            (uu____27068, uu____27071)  in
          FStar_Syntax_Syntax.Tm_app uu____27051  in
        mk1 uu____27050
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
<<<<<<< HEAD
              let uu___3385_27879 = p  in
              let uu____27880 =
                let uu____27881 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____27881  in
              {
                FStar_Syntax_Syntax.v = uu____27880;
                FStar_Syntax_Syntax.p =
                  (uu___3385_27879.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3389_27883 = p  in
              let uu____27884 =
                let uu____27885 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____27885  in
              {
                FStar_Syntax_Syntax.v = uu____27884;
                FStar_Syntax_Syntax.p =
                  (uu___3389_27883.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3395_27892 = p  in
              let uu____27893 =
                let uu____27894 =
                  let uu____27901 = elim_bv x  in
                  let uu____27902 = elim_delayed_subst_term t0  in
                  (uu____27901, uu____27902)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____27894  in
              {
                FStar_Syntax_Syntax.v = uu____27893;
                FStar_Syntax_Syntax.p =
                  (uu___3395_27892.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3401_27927 = p  in
              let uu____27928 =
                let uu____27929 =
                  let uu____27943 =
                    FStar_List.map
                      (fun uu____27969  ->
                         match uu____27969 with
                         | (x,b) ->
                             let uu____27986 = elim_pat x  in
                             (uu____27986, b)) pats
                     in
                  (fv, uu____27943)  in
                FStar_Syntax_Syntax.Pat_cons uu____27929  in
              {
                FStar_Syntax_Syntax.v = uu____27928;
                FStar_Syntax_Syntax.p =
                  (uu___3401_27927.FStar_Syntax_Syntax.p)
              }
          | uu____28001 -> p  in
        let elim_branch uu____28025 =
          match uu____28025 with
          | (pat,wopt,t3) ->
              let uu____28051 = elim_pat pat  in
              let uu____28054 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28057 = elim_delayed_subst_term t3  in
              (uu____28051, uu____28054, uu____28057)
           in
        let uu____28062 =
          let uu____28063 =
            let uu____28086 = elim_delayed_subst_term t2  in
            let uu____28089 = FStar_List.map elim_branch branches  in
            (uu____28086, uu____28089)  in
          FStar_Syntax_Syntax.Tm_match uu____28063  in
        mk1 uu____28062
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28220 =
          match uu____28220 with
          | (tc,topt) ->
              let uu____28255 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28265 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28265
                | FStar_Util.Inr c ->
                    let uu____28267 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28267
                 in
              let uu____28268 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28255, uu____28268)
           in
        let uu____28277 =
          let uu____28278 =
            let uu____28305 = elim_delayed_subst_term t2  in
            let uu____28308 = elim_ascription a  in
            (uu____28305, uu____28308, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28278  in
        mk1 uu____28277
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3431_28371 = lb  in
          let uu____28372 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____28375 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3431_28371.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3431_28371.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28372;
            FStar_Syntax_Syntax.lbeff =
              (uu___3431_28371.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28375;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3431_28371.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3431_28371.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____28378 =
          let uu____28379 =
            let uu____28393 =
              let uu____28401 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____28401)  in
            let uu____28413 = elim_delayed_subst_term t2  in
            (uu____28393, uu____28413)  in
          FStar_Syntax_Syntax.Tm_let uu____28379  in
        mk1 uu____28378
=======
              let uu___3344_27143 = p  in
              let uu____27144 =
                let uu____27145 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____27145  in
              {
                FStar_Syntax_Syntax.v = uu____27144;
                FStar_Syntax_Syntax.p =
                  (uu___3344_27143.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3348_27147 = p  in
              let uu____27148 =
                let uu____27149 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____27149  in
              {
                FStar_Syntax_Syntax.v = uu____27148;
                FStar_Syntax_Syntax.p =
                  (uu___3348_27147.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3354_27156 = p  in
              let uu____27157 =
                let uu____27158 =
                  let uu____27165 = elim_bv x  in
                  let uu____27166 = elim_delayed_subst_term t0  in
                  (uu____27165, uu____27166)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____27158  in
              {
                FStar_Syntax_Syntax.v = uu____27157;
                FStar_Syntax_Syntax.p =
                  (uu___3354_27156.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3360_27191 = p  in
              let uu____27192 =
                let uu____27193 =
                  let uu____27207 =
                    FStar_List.map
                      (fun uu____27233  ->
                         match uu____27233 with
                         | (x,b) ->
                             let uu____27250 = elim_pat x  in
                             (uu____27250, b)) pats
                     in
                  (fv, uu____27207)  in
                FStar_Syntax_Syntax.Pat_cons uu____27193  in
              {
                FStar_Syntax_Syntax.v = uu____27192;
                FStar_Syntax_Syntax.p =
                  (uu___3360_27191.FStar_Syntax_Syntax.p)
              }
          | uu____27265 -> p  in
        let elim_branch uu____27289 =
          match uu____27289 with
          | (pat,wopt,t3) ->
              let uu____27315 = elim_pat pat  in
              let uu____27318 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____27321 = elim_delayed_subst_term t3  in
              (uu____27315, uu____27318, uu____27321)
           in
        let uu____27326 =
          let uu____27327 =
            let uu____27350 = elim_delayed_subst_term t2  in
            let uu____27353 = FStar_List.map elim_branch branches  in
            (uu____27350, uu____27353)  in
          FStar_Syntax_Syntax.Tm_match uu____27327  in
        mk1 uu____27326
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____27484 =
          match uu____27484 with
          | (tc,topt) ->
              let uu____27519 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____27529 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____27529
                | FStar_Util.Inr c ->
                    let uu____27531 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____27531
                 in
              let uu____27532 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____27519, uu____27532)
           in
        let uu____27541 =
          let uu____27542 =
            let uu____27569 = elim_delayed_subst_term t2  in
            let uu____27572 = elim_ascription a  in
            (uu____27569, uu____27572, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____27542  in
        mk1 uu____27541
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3390_27635 = lb  in
          let uu____27636 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____27639 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3390_27635.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3390_27635.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____27636;
            FStar_Syntax_Syntax.lbeff =
              (uu___3390_27635.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____27639;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3390_27635.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3390_27635.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____27642 =
          let uu____27643 =
            let uu____27657 =
              let uu____27665 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____27665)  in
            let uu____27677 = elim_delayed_subst_term t2  in
            (uu____27657, uu____27677)  in
          FStar_Syntax_Syntax.Tm_let uu____27643  in
        mk1 uu____27642
>>>>>>> snap
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
<<<<<<< HEAD
        let uu____28458 =
          let uu____28459 =
            let uu____28466 = elim_delayed_subst_term tm  in
            (uu____28466, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____28459  in
        mk1 uu____28458
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____28477 =
          let uu____28478 =
            let uu____28485 = elim_delayed_subst_term t2  in
            let uu____28488 = elim_delayed_subst_meta md  in
            (uu____28485, uu____28488)  in
          FStar_Syntax_Syntax.Tm_meta uu____28478  in
        mk1 uu____28477
=======
        let uu____27722 =
          let uu____27723 =
            let uu____27730 = elim_delayed_subst_term tm  in
            (uu____27730, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____27723  in
        mk1 uu____27722
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____27741 =
          let uu____27742 =
            let uu____27749 = elim_delayed_subst_term t2  in
            let uu____27752 = elim_delayed_subst_meta md  in
            (uu____27749, uu____27752)  in
          FStar_Syntax_Syntax.Tm_meta uu____27742  in
        mk1 uu____27741
>>>>>>> snap

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
<<<<<<< HEAD
      (fun uu___18_28497  ->
         match uu___18_28497 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28501 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____28501
=======
      (fun uu___17_27761  ->
         match uu___17_27761 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____27765 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____27765
>>>>>>> snap
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
<<<<<<< HEAD
        let uu____28524 =
          let uu____28525 =
            let uu____28534 = elim_delayed_subst_term t  in
            (uu____28534, uopt)  in
          FStar_Syntax_Syntax.Total uu____28525  in
        mk1 uu____28524
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____28551 =
          let uu____28552 =
            let uu____28561 = elim_delayed_subst_term t  in
            (uu____28561, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____28552  in
        mk1 uu____28551
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3464_28570 = ct  in
          let uu____28571 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____28574 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____28585 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3464_28570.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3464_28570.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28571;
            FStar_Syntax_Syntax.effect_args = uu____28574;
            FStar_Syntax_Syntax.flags = uu____28585
=======
        let uu____27788 =
          let uu____27789 =
            let uu____27798 = elim_delayed_subst_term t  in
            (uu____27798, uopt)  in
          FStar_Syntax_Syntax.Total uu____27789  in
        mk1 uu____27788
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____27815 =
          let uu____27816 =
            let uu____27825 = elim_delayed_subst_term t  in
            (uu____27825, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____27816  in
        mk1 uu____27815
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3423_27834 = ct  in
          let uu____27835 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____27838 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____27849 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3423_27834.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3423_27834.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____27835;
            FStar_Syntax_Syntax.effect_args = uu____27838;
            FStar_Syntax_Syntax.flags = uu____27849
>>>>>>> snap
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
<<<<<<< HEAD
  fun uu___19_28588  ->
    match uu___19_28588 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____28623 =
          let uu____28644 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____28653 = FStar_List.map elim_delayed_subst_args args  in
          (uu____28644, uu____28653)  in
        FStar_Syntax_Syntax.Meta_pattern uu____28623
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____28708 =
          let uu____28715 = elim_delayed_subst_term t  in (m, uu____28715)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____28708
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____28727 =
          let uu____28736 = elim_delayed_subst_term t  in
          (m1, m2, uu____28736)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____28727
=======
  fun uu___18_27852  ->
    match uu___18_27852 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____27887 =
          let uu____27908 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____27917 = FStar_List.map elim_delayed_subst_args args  in
          (uu____27908, uu____27917)  in
        FStar_Syntax_Syntax.Meta_pattern uu____27887
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____27972 =
          let uu____27979 = elim_delayed_subst_term t  in (m, uu____27979)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____27972
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____27991 =
          let uu____28000 = elim_delayed_subst_term t  in
          (m1, m2, uu____28000)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____27991
>>>>>>> snap
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
<<<<<<< HEAD
      (fun uu____28769  ->
         match uu____28769 with
         | (t,q) ->
             let uu____28788 = elim_delayed_subst_term t  in (uu____28788, q))
=======
      (fun uu____28033  ->
         match uu____28033 with
         | (t,q) ->
             let uu____28052 = elim_delayed_subst_term t  in (uu____28052, q))
>>>>>>> snap
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
<<<<<<< HEAD
      (fun uu____28816  ->
         match uu____28816 with
         | (x,q) ->
             let uu____28835 =
               let uu___3490_28836 = x  in
               let uu____28837 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3490_28836.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3490_28836.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____28837
               }  in
             (uu____28835, q)) bs
=======
      (fun uu____28080  ->
         match uu____28080 with
         | (x,q) ->
             let uu____28099 =
               let uu___3449_28100 = x  in
               let uu____28101 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3449_28100.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3449_28100.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____28101
               }  in
             (uu____28099, q)) bs
>>>>>>> snap

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
<<<<<<< HEAD
            | (uu____28945,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____28977,FStar_Util.Inl t) ->
                let uu____28999 =
                  let uu____29006 =
                    let uu____29007 =
                      let uu____29022 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29022)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29007  in
                  FStar_Syntax_Syntax.mk uu____29006  in
                uu____28999 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29035 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29035 with
=======
            | (uu____28209,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____28241,FStar_Util.Inl t) ->
                let uu____28263 =
                  let uu____28270 =
                    let uu____28271 =
                      let uu____28286 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____28286)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____28271  in
                  FStar_Syntax_Syntax.mk uu____28270  in
                uu____28263 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____28299 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____28299 with
>>>>>>> snap
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
<<<<<<< HEAD
              let uu____29067 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29140 ->
                    let uu____29141 =
                      let uu____29150 =
                        let uu____29151 = FStar_Syntax_Subst.compress t4  in
                        uu____29151.FStar_Syntax_Syntax.n  in
                      (uu____29150, tc)  in
                    (match uu____29141 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29180) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29227) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29272,FStar_Util.Inl uu____29273) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29304 -> failwith "Impossible")
                 in
              (match uu____29067 with
=======
              let uu____28331 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____28404 ->
                    let uu____28405 =
                      let uu____28414 =
                        let uu____28415 = FStar_Syntax_Subst.compress t4  in
                        uu____28415.FStar_Syntax_Syntax.n  in
                      (uu____28414, tc)  in
                    (match uu____28405 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____28444) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____28491) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____28536,FStar_Util.Inl uu____28537) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____28568 -> failwith "Impossible")
                 in
              (match uu____28331 with
>>>>>>> snap
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
<<<<<<< HEAD
          let uu____29443 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____29443 with
          | (univ_names1,binders1,tc) ->
              let uu____29517 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____29517)
=======
          let uu____28707 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____28707 with
          | (univ_names1,binders1,tc) ->
              let uu____28781 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____28781)
>>>>>>> snap
  
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
<<<<<<< HEAD
          let uu____29571 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____29571 with
          | (univ_names1,binders1,tc) ->
              let uu____29645 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____29645)
=======
          let uu____28835 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____28835 with
          | (univ_names1,binders1,tc) ->
              let uu____28909 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____28909)
>>>>>>> snap
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
<<<<<<< HEAD
          let uu____29687 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____29687 with
           | (univ_names1,binders1,typ1) ->
               let uu___3573_29727 = s  in
=======
          let uu____28951 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____28951 with
           | (univ_names1,binders1,typ1) ->
               let uu___3532_28991 = s  in
>>>>>>> snap
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                   (uu___3573_29727.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3573_29727.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3573_29727.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3573_29727.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3579_29742 = s  in
          let uu____29743 =
            let uu____29744 =
              let uu____29753 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29753, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29744  in
          {
            FStar_Syntax_Syntax.sigel = uu____29743;
            FStar_Syntax_Syntax.sigrng =
              (uu___3579_29742.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3579_29742.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3579_29742.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3579_29742.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29772 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29772 with
           | (univ_names1,uu____29796,typ1) ->
               let uu___3593_29818 = s  in
=======
                   (uu___3532_28991.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3532_28991.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3532_28991.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3532_28991.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3538_29006 = s  in
          let uu____29007 =
            let uu____29008 =
              let uu____29017 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29017, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29008  in
          {
            FStar_Syntax_Syntax.sigel = uu____29007;
            FStar_Syntax_Syntax.sigrng =
              (uu___3538_29006.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3538_29006.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3538_29006.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3538_29006.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29036 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29036 with
           | (univ_names1,uu____29060,typ1) ->
               let uu___3552_29082 = s  in
>>>>>>> snap
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                   (uu___3593_29818.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3593_29818.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3593_29818.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3593_29818.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____29825 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29825 with
           | (univ_names1,uu____29849,typ1) ->
               let uu___3604_29871 = s  in
=======
                   (uu___3552_29082.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3552_29082.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3552_29082.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3552_29082.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____29089 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29089 with
           | (univ_names1,uu____29113,typ1) ->
               let uu___3563_29135 = s  in
>>>>>>> snap
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                   (uu___3604_29871.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3604_29871.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3604_29871.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3604_29871.FStar_Syntax_Syntax.sigattrs)
=======
                   (uu___3563_29135.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3563_29135.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3563_29135.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3563_29135.FStar_Syntax_Syntax.sigattrs)
>>>>>>> snap
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
<<<<<<< HEAD
                    let uu____29901 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____29901 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____29926 =
                            let uu____29927 =
                              let uu____29928 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____29928  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____29927
                             in
                          elim_delayed_subst_term uu____29926  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3620_29931 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3620_29931.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3620_29931.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3620_29931.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3620_29931.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3623_29932 = s  in
=======
                    let uu____29165 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____29165 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____29190 =
                            let uu____29191 =
                              let uu____29192 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____29192  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____29191
                             in
                          elim_delayed_subst_term uu____29190  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3579_29195 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3579_29195.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3579_29195.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3579_29195.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3579_29195.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3582_29196 = s  in
>>>>>>> snap
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
              (uu___3623_29932.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3623_29932.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3623_29932.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3623_29932.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3627_29939 = s  in
          let uu____29940 =
            let uu____29941 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____29941  in
          {
            FStar_Syntax_Syntax.sigel = uu____29940;
            FStar_Syntax_Syntax.sigrng =
              (uu___3627_29939.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3627_29939.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3627_29939.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3627_29939.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____29945 = elim_uvars_aux_t env us [] t  in
          (match uu____29945 with
           | (us1,uu____29969,t1) ->
               let uu___3638_29991 = s  in
=======
              (uu___3582_29196.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3582_29196.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3582_29196.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3582_29196.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3586_29203 = s  in
          let uu____29204 =
            let uu____29205 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____29205  in
          {
            FStar_Syntax_Syntax.sigel = uu____29204;
            FStar_Syntax_Syntax.sigrng =
              (uu___3586_29203.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3586_29203.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3586_29203.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3586_29203.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____29209 = elim_uvars_aux_t env us [] t  in
          (match uu____29209 with
           | (us1,uu____29233,t1) ->
               let uu___3597_29255 = s  in
>>>>>>> snap
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                   (uu___3638_29991.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3638_29991.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3638_29991.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3638_29991.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____29992 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____29995 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____29995 with
           | (univs1,binders,uu____30014) ->
               let uu____30035 =
                 let uu____30040 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____30040 with
                 | (univs_opening,univs2) ->
                     let uu____30063 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____30063)
                  in
               (match uu____30035 with
                | (univs_opening,univs_closing) ->
                    let uu____30066 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30072 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30073 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30072, uu____30073)  in
                    (match uu____30066 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30099 =
                           match uu____30099 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30117 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30117 with
                                | (us1,t1) ->
                                    let uu____30128 =
                                      let uu____30137 =
=======
                   (uu___3597_29255.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3597_29255.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3597_29255.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3597_29255.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____29256 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____29259 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____29259 with
           | (univs1,binders,uu____29278) ->
               let uu____29299 =
                 let uu____29304 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____29304 with
                 | (univs_opening,univs2) ->
                     let uu____29327 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____29327)
                  in
               (match uu____29299 with
                | (univs_opening,univs_closing) ->
                    let uu____29330 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____29336 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____29337 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____29336, uu____29337)  in
                    (match uu____29330 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____29363 =
                           match uu____29363 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____29381 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____29381 with
                                | (us1,t1) ->
                                    let uu____29392 =
                                      let uu____29401 =
>>>>>>> snap
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
<<<<<<< HEAD
                                      let uu____30142 =
=======
                                      let uu____29406 =
>>>>>>> snap
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
<<<<<<< HEAD
                                      (uu____30137, uu____30142)  in
                                    (match uu____30128 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30165 =
                                           let uu____30174 =
=======
                                      (uu____29401, uu____29406)  in
                                    (match uu____29392 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____29429 =
                                           let uu____29438 =
>>>>>>> snap
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
<<<<<<< HEAD
                                           let uu____30179 =
=======
                                           let uu____29443 =
>>>>>>> snap
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
<<<<<<< HEAD
                                           (uu____30174, uu____30179)  in
                                         (match uu____30165 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30203 =
=======
                                           (uu____29438, uu____29443)  in
                                         (match uu____29429 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____29467 =
>>>>>>> snap
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
<<<<<<< HEAD
                                                  univs_opening1 uu____30203
                                                 in
                                              let uu____30204 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30204 with
                                               | (uu____30231,uu____30232,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30255 =
                                                       let uu____30256 =
=======
                                                  univs_opening1 uu____29467
                                                 in
                                              let uu____29468 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____29468 with
                                               | (uu____29495,uu____29496,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____29519 =
                                                       let uu____29520 =
>>>>>>> snap
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
<<<<<<< HEAD
                                                         uu____30256
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30255
=======
                                                         uu____29520
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____29519
>>>>>>> snap
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
<<<<<<< HEAD
                           let uu____30265 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____30265 with
                           | (uu____30284,uu____30285,t1) -> t1  in
=======
                           let uu____29529 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____29529 with
                           | (uu____29548,uu____29549,t1) -> t1  in
>>>>>>> snap
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
<<<<<<< HEAD
                             | uu____30361 ->
=======
                             | uu____29625 ->
>>>>>>> snap
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
<<<<<<< HEAD
                             let uu____30388 =
                               let uu____30389 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____30389.FStar_Syntax_Syntax.n  in
                             match uu____30388 with
=======
                             let uu____29652 =
                               let uu____29653 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____29653.FStar_Syntax_Syntax.n  in
                             match uu____29652 with
>>>>>>> snap
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
<<<<<<< HEAD
                             | uu____30448 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____30482 =
                               let uu____30483 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____30483.FStar_Syntax_Syntax.n  in
                             match uu____30482 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____30506) ->
                                 let uu____30531 = destruct_action_body body
                                    in
                                 (match uu____30531 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____30580 ->
                                 let uu____30581 = destruct_action_body t  in
                                 (match uu____30581 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____30636 =
=======
                             | uu____29712 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____29746 =
                               let uu____29747 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____29747.FStar_Syntax_Syntax.n  in
                             match uu____29746 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____29770) ->
                                 let uu____29795 = destruct_action_body body
                                    in
                                 (match uu____29795 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____29844 ->
                                 let uu____29845 = destruct_action_body t  in
                                 (match uu____29845 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____29900 =
>>>>>>> snap
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
<<<<<<< HEAD
                           match uu____30636 with
                           | (action_univs,t) ->
                               let uu____30645 = destruct_action_typ_templ t
                                  in
                               (match uu____30645 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3724_30692 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3724_30692.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3724_30692.FStar_Syntax_Syntax.action_unqualified_name);
=======
                           match uu____29900 with
                           | (action_univs,t) ->
                               let uu____29909 = destruct_action_typ_templ t
                                  in
                               (match uu____29909 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3683_29956 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3683_29956.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3683_29956.FStar_Syntax_Syntax.action_unqualified_name);
>>>>>>> snap
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
<<<<<<< HEAD
                           let uu___3727_30694 = ed  in
                           let uu____30695 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____30696 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____30697 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____30698 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____30699 =
                             FStar_Syntax_Util.map_match_wps elim_tscheme
                               ed.FStar_Syntax_Syntax.match_wps
                              in
                           let uu____30704 =
                             FStar_Util.map_opt
                               ed.FStar_Syntax_Syntax.trivial elim_tscheme
                              in
                           let uu____30707 =
                             elim_tscheme ed.FStar_Syntax_Syntax.repr  in
                           let uu____30708 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____30709 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____30710 =
                             FStar_Util.map_opt
                               ed.FStar_Syntax_Syntax.stronger_repr
                               elim_tscheme
                              in
                           let uu____30713 =
=======
                           let uu___3686_29958 = ed  in
                           let uu____29959 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____29960 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____29961 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____29962 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____29963 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____29964 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____29965 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____29966 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____29967 =
                             elim_tscheme ed.FStar_Syntax_Syntax.repr  in
                           let uu____29968 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____29969 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____29970 =
>>>>>>> snap
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.is_layered =
                               (uu___3727_30694.FStar_Syntax_Syntax.is_layered);
                             FStar_Syntax_Syntax.cattributes =
<<<<<<< HEAD
                               (uu___3727_30694.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___3727_30694.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____30695;
                             FStar_Syntax_Syntax.ret_wp = uu____30696;
                             FStar_Syntax_Syntax.bind_wp = uu____30697;
                             FStar_Syntax_Syntax.stronger = uu____30698;
                             FStar_Syntax_Syntax.match_wps = uu____30699;
                             FStar_Syntax_Syntax.trivial = uu____30704;
                             FStar_Syntax_Syntax.repr = uu____30707;
                             FStar_Syntax_Syntax.return_repr = uu____30708;
                             FStar_Syntax_Syntax.bind_repr = uu____30709;
                             FStar_Syntax_Syntax.stronger_repr = uu____30710;
                             FStar_Syntax_Syntax.actions = uu____30713;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3727_30694.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3730_30716 = s  in
=======
                               (uu___3686_29958.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___3686_29958.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____29959;
                             FStar_Syntax_Syntax.ret_wp = uu____29960;
                             FStar_Syntax_Syntax.bind_wp = uu____29961;
                             FStar_Syntax_Syntax.if_then_else = uu____29962;
                             FStar_Syntax_Syntax.ite_wp = uu____29963;
                             FStar_Syntax_Syntax.stronger = uu____29964;
                             FStar_Syntax_Syntax.close_wp = uu____29965;
                             FStar_Syntax_Syntax.trivial = uu____29966;
                             FStar_Syntax_Syntax.repr = uu____29967;
                             FStar_Syntax_Syntax.return_repr = uu____29968;
                             FStar_Syntax_Syntax.bind_repr = uu____29969;
                             FStar_Syntax_Syntax.actions = uu____29970;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3686_29958.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3689_29973 = s  in
>>>>>>> snap
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                             (uu___3730_30716.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3730_30716.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3730_30716.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3730_30716.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___20_30737 =
            match uu___20_30737 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30768 = elim_uvars_aux_t env us [] t  in
                (match uu____30768 with
                 | (us1,uu____30800,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3745_30831 = sub_eff  in
            let uu____30832 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____30835 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3745_30831.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3745_30831.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30832;
              FStar_Syntax_Syntax.lift = uu____30835
            }  in
          let uu___3748_30838 = s  in
=======
                             (uu___3689_29973.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3689_29973.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3689_29973.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3689_29973.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_29994 =
            match uu___19_29994 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30025 = elim_uvars_aux_t env us [] t  in
                (match uu____30025 with
                 | (us1,uu____30057,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3704_30088 = sub_eff  in
            let uu____30089 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____30092 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3704_30088.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3704_30088.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30089;
              FStar_Syntax_Syntax.lift = uu____30092
            }  in
          let uu___3707_30095 = s  in
>>>>>>> snap
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
              (uu___3748_30838.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3748_30838.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3748_30838.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3748_30838.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____30848 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____30848 with
           | (univ_names1,binders1,comp1) ->
               let uu___3761_30888 = s  in
=======
              (uu___3707_30095.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3707_30095.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3707_30095.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3707_30095.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____30105 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____30105 with
           | (univ_names1,binders1,comp1) ->
               let uu___3720_30145 = s  in
>>>>>>> snap
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
<<<<<<< HEAD
                   (uu___3761_30888.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3761_30888.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3761_30888.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3761_30888.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____30891 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____30892 -> s
=======
                   (uu___3720_30145.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3720_30145.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3720_30145.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3720_30145.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____30148 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____30149 -> s
>>>>>>> snap
  
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
<<<<<<< HEAD
        let uu____30941 =
=======
        let uu____30198 =
>>>>>>> snap
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
<<<<<<< HEAD
        match uu____30941 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____30963 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____30963 with
             | (uu____30970,head_def) ->
=======
        match uu____30198 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____30220 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____30220 with
             | (uu____30227,head_def) ->
>>>>>>> snap
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
<<<<<<< HEAD
      let uu____30976 = FStar_Syntax_Util.head_and_args t  in
      match uu____30976 with
      | (head1,args) ->
          let uu____31021 =
            let uu____31022 = FStar_Syntax_Subst.compress head1  in
            uu____31022.FStar_Syntax_Syntax.n  in
          (match uu____31021 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31029;
                  FStar_Syntax_Syntax.vars = uu____31030;_},us)
               -> aux fv us args
           | uu____31036 -> FStar_Pervasives_Native.None)
=======
      let uu____30233 = FStar_Syntax_Util.head_and_args t  in
      match uu____30233 with
      | (head1,args) ->
          let uu____30278 =
            let uu____30279 = FStar_Syntax_Subst.compress head1  in
            uu____30279.FStar_Syntax_Syntax.n  in
          (match uu____30278 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____30286;
                  FStar_Syntax_Syntax.vars = uu____30287;_},us)
               -> aux fv us args
           | uu____30293 -> FStar_Pervasives_Native.None)
>>>>>>> snap
  