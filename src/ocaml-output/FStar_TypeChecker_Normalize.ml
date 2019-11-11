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
                        FStar_Syntax_Syntax.sigattrs = uu____7768;
                        FStar_Syntax_Syntax.sigopts = uu____7769;_},uu____7770),uu____7771),uu____7772,uu____7773,uu____7774)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7883  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7885,uu____7886,uu____7887,uu____7888) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7955  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7958),uu____7959);
                        FStar_Syntax_Syntax.sigrng = uu____7960;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7962;
                        FStar_Syntax_Syntax.sigattrs = uu____7963;
                        FStar_Syntax_Syntax.sigopts = uu____7964;_},uu____7965),uu____7966),uu____7967,uu____7968,uu____7969)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8078  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8080,FStar_Pervasives_Native.Some
                    uu____8081,uu____8082,uu____8083) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8151  ->
                           let uu____8152 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8152);
                      (let uu____8155 =
                         let uu____8167 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8193 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8193
                            in
                         let uu____8205 =
                           let uu____8217 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8243 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8243
                              in
                           let uu____8259 =
                             let uu____8271 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8297 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8297
                                in
                             [uu____8271]  in
                           uu____8217 :: uu____8259  in
                         uu____8167 :: uu____8205  in
                       comb_or uu____8155))
                 | (uu____8345,uu____8346,FStar_Pervasives_Native.Some
                    uu____8347,uu____8348) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8416  ->
                           let uu____8417 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8417);
                      (let uu____8420 =
                         let uu____8432 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8458 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8458
                            in
                         let uu____8470 =
                           let uu____8482 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8508 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8508
                              in
                           let uu____8524 =
                             let uu____8536 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8562 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8562
                                in
                             [uu____8536]  in
                           uu____8482 :: uu____8524  in
                         uu____8432 :: uu____8470  in
                       comb_or uu____8420))
                 | (uu____8610,uu____8611,uu____8612,FStar_Pervasives_Native.Some
                    uu____8613) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8681  ->
                           let uu____8682 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8682);
                      (let uu____8685 =
                         let uu____8697 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8723 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8723
                            in
                         let uu____8735 =
                           let uu____8747 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8773 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8773
                              in
                           let uu____8789 =
                             let uu____8801 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8827 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8827
                                in
                             [uu____8801]  in
                           uu____8747 :: uu____8789  in
                         uu____8697 :: uu____8735  in
                       comb_or uu____8685))
                 | uu____8875 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8921  ->
                           let uu____8922 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____8924 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____8926 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____8922 uu____8924 uu____8926);
                      (let uu____8929 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___12_8935  ->
                                 match uu___12_8935 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____8941 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____8941 l))
                          in
                       FStar_All.pipe_left yesno uu____8929)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____8957  ->
               let uu____8958 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____8960 =
                 let uu____8962 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____8962  in
               let uu____8963 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____8958 uu____8960 uu____8963);
          (match res with
           | (false ,uu____8966,uu____8967) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____8992 ->
               let uu____9002 =
                 let uu____9004 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9004
                  in
               FStar_All.pipe_left failwith uu____9002)
  
let decide_unfolding :
  'Auu____9023 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____9023 ->
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
                    let uu___1146_9092 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1148_9095 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1148_9095.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1148_9095.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1146_9092.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1146_9092.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1146_9092.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1146_9092.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1146_9092.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1146_9092.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1146_9092.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1146_9092.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____9157 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____9157
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9169 =
                      let uu____9176 =
                        let uu____9177 =
                          let uu____9178 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____9178  in
                        FStar_Syntax_Syntax.Tm_constant uu____9177  in
                      FStar_Syntax_Syntax.mk uu____9176  in
                    uu____9169 FStar_Pervasives_Native.None
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
    let uu____9244 =
      let uu____9245 = FStar_Syntax_Subst.compress t  in
      uu____9245.FStar_Syntax_Syntax.n  in
    match uu____9244 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9276 =
          let uu____9277 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9277.FStar_Syntax_Syntax.n  in
        (match uu____9276 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9294 =
                 let uu____9301 =
                   let uu____9312 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9312 FStar_List.tl  in
                 FStar_All.pipe_right uu____9301 FStar_List.hd  in
               FStar_All.pipe_right uu____9294 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9411 -> FStar_Pervasives_Native.None)
    | uu____9412 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9691 ->
                   let uu____9714 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9714
               | uu____9717 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9727  ->
               let uu____9728 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9730 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9732 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9734 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9742 =
                 let uu____9744 =
                   let uu____9747 = firstn (Prims.of_int (4)) stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9747
                    in
                 stack_to_string uu____9744  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9728 uu____9730 uu____9732 uu____9734 uu____9742);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9775  ->
               let uu____9776 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9776);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9782  ->
                     let uu____9783 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9783);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9786 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9790  ->
                     let uu____9791 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9791);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____9794 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9798  ->
                     let uu____9799 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9799);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9802 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9806  ->
                     let uu____9807 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9807);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9810;
                 FStar_Syntax_Syntax.fv_delta = uu____9811;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9815  ->
                     let uu____9816 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9816);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9819;
                 FStar_Syntax_Syntax.fv_delta = uu____9820;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9821);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9831  ->
                     let uu____9832 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9832);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____9838 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____9838 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _9841) when
                    _9841 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9845  ->
                          let uu____9846 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9846);
                     rebuild cfg env stack t1)
                | uu____9849 ->
                    let uu____9852 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____9852 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____9879 ->
               let uu____9886 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____9886
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9914 = is_norm_request hd1 args  in
                  uu____9914 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____9920 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____9920))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9948 = is_norm_request hd1 args  in
                  uu____9948 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1255_9955 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1257_9958 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1257_9958.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1255_9955.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1255_9955.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1255_9955.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1255_9955.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1255_9955.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1255_9955.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____9965 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____9965 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____10001  ->
                                 fun stack1  ->
                                   match uu____10001 with
                                   | (a,aq) ->
                                       let uu____10013 =
                                         let uu____10014 =
                                           let uu____10021 =
                                             let uu____10022 =
                                               let uu____10054 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____10054, false)
                                                in
                                             Clos uu____10022  in
                                           (uu____10021, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10014  in
                                       uu____10013 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10122  ->
                            let uu____10123 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10123);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10150 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____10150)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____10161 =
                            let uu____10163 =
                              let uu____10165 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____10165  in
                            FStar_Util.string_of_int uu____10163  in
                          let uu____10172 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____10174 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____10161 uu____10172 uu____10174)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10193 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____10193)
                      else ();
                      (let delta_level =
                         let uu____10201 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___13_10208  ->
                                   match uu___13_10208 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____10210 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____10212 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____10216 -> true
                                   | uu____10220 -> false))
                            in
                         if uu____10201
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1298_10228 = cfg  in
                         let uu____10229 =
                           let uu___1300_10230 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1300_10230.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____10229;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1298_10228.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1298_10228.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1298_10228.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1298_10228.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1298_10228.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1298_10228.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____10238 =
                             let uu____10239 =
                               let uu____10244 = FStar_Util.now ()  in
                               (t1, uu____10244)  in
                             Debug uu____10239  in
                           uu____10238 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10249 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10249
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10260 =
                      let uu____10267 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10267, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10260  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10276 = lookup_bvar env x  in
               (match uu____10276 with
                | Univ uu____10277 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____10331 = FStar_ST.op_Bang r  in
                      (match uu____10331 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10427  ->
                                 let uu____10428 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10430 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10428
                                   uu____10430);
                            (let uu____10433 = maybe_weakly_reduced t'  in
                             if uu____10433
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____10436 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10480)::uu____10481 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10492,uu____10493))::stack_rest ->
                    (match c with
                     | Univ uu____10497 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10506 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10536  ->
                                    let uu____10537 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10537);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10573  ->
                                    let uu____10574 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10574);
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
                       (fun uu____10622  ->
                          let uu____10623 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10623);
                     norm cfg env stack1 t1)
                | (Match uu____10626)::uu____10627 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10642 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10642 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10678  -> dummy :: env1) env)
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
                                          let uu____10722 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10722)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1418_10730 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1418_10730.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1418_10730.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10731 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10737  ->
                                 let uu____10738 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10738);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1425_10753 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1425_10753.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1425_10753.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1425_10753.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1425_10753.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1425_10753.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1425_10753.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1425_10753.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1425_10753.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____10757)::uu____10758 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10769 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10769 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10805  -> dummy :: env1) env)
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
                                   (let uu___1418_10857 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1418_10857.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1418_10857.FStar_Syntax_Syntax.residual_flags)
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
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1425_10880 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1425_10880.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1425_10880.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1425_10880.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1425_10880.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1425_10880.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1425_10880.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1425_10880.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1425_10880.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10884)::uu____10885 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10898 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10898 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10934  -> dummy :: env1) env)
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
                                          let uu____10978 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10978)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1418_10986 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1418_10986.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1418_10986.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10987 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10993  ->
                                 let uu____10994 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10994);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1425_11009 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1425_11009.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1425_11009.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1425_11009.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1425_11009.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1425_11009.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1425_11009.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1425_11009.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1425_11009.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11013)::uu____11014 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11029 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11029 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11065  -> dummy :: env1) env)
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
                                          let uu____11109 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11109)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1418_11117 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1418_11117.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1418_11117.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11118 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11124  ->
                                 let uu____11125 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11125);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1425_11140 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1425_11140.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1425_11140.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1425_11140.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1425_11140.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1425_11140.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1425_11140.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1425_11140.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1425_11140.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11144)::uu____11145 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11160 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11160 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11196  -> dummy :: env1) env)
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
                                          let uu____11240 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11240)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1418_11248 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1418_11248.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1418_11248.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11249 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11255  ->
                                 let uu____11256 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11256);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1425_11271 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1425_11271.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1425_11271.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1425_11271.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1425_11271.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1425_11271.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1425_11271.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1425_11271.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1425_11271.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11275)::uu____11276 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11295 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11295 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11331  -> dummy :: env1) env)
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
                                          let uu____11375 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11375)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1418_11383 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1418_11383.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1418_11383.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11384 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11390  ->
                                 let uu____11391 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11391);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1425_11406 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1425_11406.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1425_11406.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1425_11406.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1425_11406.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1425_11406.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1425_11406.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1425_11406.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1425_11406.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____11414 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11414 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11450  -> dummy :: env1) env)
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
                                          let uu____11494 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11494)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1418_11502 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1418_11502.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1418_11502.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11503 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11509  ->
                                 let uu____11510 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11510);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1425_11525 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1425_11525.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1425_11525.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1425_11525.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1425_11525.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1425_11525.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1425_11525.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1425_11525.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1425_11525.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let strict_args =
                 let uu____11561 =
                   let uu____11562 = FStar_Syntax_Util.un_uinst head1  in
                   uu____11562.FStar_Syntax_Syntax.n  in
                 match uu____11561 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11571 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11592  ->
                              fun stack1  ->
                                match uu____11592 with
                                | (a,aq) ->
                                    let uu____11604 =
                                      let uu____11605 =
                                        let uu____11612 =
                                          let uu____11613 =
                                            let uu____11645 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11645, false)  in
                                          Clos uu____11613  in
                                        (uu____11612, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11605  in
                                    uu____11604 :: stack1) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11713  ->
                          let uu____11714 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11714);
                     norm cfg env stack1 head1)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____11765  ->
                              match uu____11765 with
                              | (a,i) ->
                                  let uu____11776 = norm cfg env [] a  in
                                  (uu____11776, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____11782 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____11797 = FStar_List.nth norm_args i
                                    in
                                 match uu____11797 with
                                 | (arg_i,uu____11808) ->
                                     let uu____11809 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____11809 with
                                      | (head2,uu____11828) ->
                                          let uu____11853 =
                                            let uu____11854 =
                                              FStar_Syntax_Util.un_uinst
                                                head2
                                               in
                                            uu____11854.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____11853 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____11858 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____11861 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____11861
                                           | uu____11862 -> false)))))
                       in
                    if uu____11782
                    then
                      let stack1 =
                        FStar_All.pipe_right stack
                          (FStar_List.fold_right
                             (fun uu____11879  ->
                                fun stack1  ->
                                  match uu____11879 with
                                  | (a,aq) ->
                                      let uu____11891 =
                                        let uu____11892 =
                                          let uu____11899 =
                                            let uu____11900 =
                                              let uu____11932 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env, a, uu____11932, false)
                                               in
                                            Clos uu____11900  in
                                          (uu____11899, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____11892  in
                                      uu____11891 :: stack1) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12014  ->
                            let uu____12015 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12015);
                       norm cfg env stack1 head1)
                    else
                      (let head2 = closure_as_term cfg env head1  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                           FStar_Pervasives_Native.None
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env stack term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12035) when
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
                             ((let uu___1487_12080 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1487_12080.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1487_12080.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12081 ->
                      let uu____12096 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12096)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12100 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12100 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12131 =
                          let uu____12132 =
                            let uu____12139 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1496_12145 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1496_12145.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1496_12145.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12139)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12132  in
                        mk uu____12131 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12169 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12169
               else
                 (let uu____12172 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12172 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12180 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12206  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12180 c1  in
                      let t2 =
                        let uu____12230 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12230 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12343)::uu____12344 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12357  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12359)::uu____12360 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12371  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12373,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12374;
                                   FStar_Syntax_Syntax.vars = uu____12375;_},uu____12376,uu____12377))::uu____12378
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12385  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12387)::uu____12388 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12399  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12401 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12404  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12409  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12435 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12435
                         | FStar_Util.Inr c ->
                             let uu____12449 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12449
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12472 =
                               let uu____12473 =
                                 let uu____12500 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12500, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12473
                                in
                             mk uu____12472 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12535 ->
                           let uu____12536 =
                             let uu____12537 =
                               let uu____12538 =
                                 let uu____12565 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12565, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12538
                                in
                             mk uu____12537 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12536))))
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
                   let uu___1575_12643 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1577_12646 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1577_12646.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1575_12643.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1575_12643.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1575_12643.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1575_12643.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1575_12643.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1575_12643.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1575_12643.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1575_12643.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____12687 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12687 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1590_12707 = cfg  in
                               let uu____12708 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1590_12707.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12708;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1590_12707.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1590_12707.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1590_12707.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1590_12707.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1590_12707.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1590_12707.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1590_12707.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____12715 =
                                 let uu____12716 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12716  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12715
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1597_12719 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1597_12719.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1597_12719.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1597_12719.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1597_12719.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12720 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12720
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12733,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12734;
                               FStar_Syntax_Syntax.lbunivs = uu____12735;
                               FStar_Syntax_Syntax.lbtyp = uu____12736;
                               FStar_Syntax_Syntax.lbeff = uu____12737;
                               FStar_Syntax_Syntax.lbdef = uu____12738;
                               FStar_Syntax_Syntax.lbattrs = uu____12739;
                               FStar_Syntax_Syntax.lbpos = uu____12740;_}::uu____12741),uu____12742)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12788 =
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
               if uu____12788
               then
                 let binder =
                   let uu____12792 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12792  in
                 let env1 =
                   let uu____12802 =
                     let uu____12809 =
                       let uu____12810 =
                         let uu____12842 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12842,
                           false)
                          in
                       Clos uu____12810  in
                     ((FStar_Pervasives_Native.Some binder), uu____12809)  in
                   uu____12802 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____12917  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____12924  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12926 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12926))
                 else
                   (let uu____12929 =
                      let uu____12934 =
                        let uu____12935 =
                          let uu____12942 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12942
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12935]  in
                      FStar_Syntax_Subst.open_term uu____12934 body  in
                    match uu____12929 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____12969  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12978 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12978  in
                            FStar_Util.Inl
                              (let uu___1639_12994 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1639_12994.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1639_12994.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____12997  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___1644_13000 = lb  in
                             let uu____13001 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1644_13000.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1644_13000.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13001;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1644_13000.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1644_13000.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13030  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___1651_13055 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___1651_13055.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___1651_13055.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___1651_13055.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___1651_13055.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___1651_13055.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___1651_13055.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___1651_13055.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___1651_13055.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____13059  ->
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
               let uu____13080 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13080 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13116 =
                               let uu___1667_13117 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1667_13117.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1667_13117.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13116  in
                           let uu____13118 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13118 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13144 =
                                   FStar_List.map (fun uu____13160  -> dummy)
                                     lbs1
                                    in
                                 let uu____13161 =
                                   let uu____13170 =
                                     FStar_List.map
                                       (fun uu____13192  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13170 env  in
                                 FStar_List.append uu____13144 uu____13161
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13218 =
                                       let uu___1681_13219 = rc  in
                                       let uu____13220 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1681_13219.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13220;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1681_13219.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13218
                                 | uu____13229 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1686_13235 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1686_13235.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1686_13235.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1686_13235.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1686_13235.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13245 =
                        FStar_List.map (fun uu____13261  -> dummy) lbs2  in
                      FStar_List.append uu____13245 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13269 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13269 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1695_13285 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1695_13285.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1695_13285.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____13319 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13319
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13340 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13418  ->
                        match uu____13418 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1711_13543 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1711_13543.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1711_13543.FStar_Syntax_Syntax.sort)
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
               (match uu____13340 with
                | (rec_env,memos,uu____13734) ->
                    let uu____13789 =
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
                             let uu____14038 =
                               let uu____14045 =
                                 let uu____14046 =
                                   let uu____14078 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14078, false)
                                    in
                                 Clos uu____14046  in
                               (FStar_Pervasives_Native.None, uu____14045)
                                in
                             uu____14038 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14163  ->
                     let uu____14164 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14164);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14188 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14192::uu____14193 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14198) ->
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
                             | uu____14277 -> norm cfg env stack head1)
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
                                  let uu____14325 =
                                    let uu____14346 =
                                      norm_pattern_args cfg env args  in
                                    (names2, uu____14346)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14325
                              | uu____14375 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14381 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14405 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14419 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14433 =
                        let uu____14435 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14437 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14435 uu____14437
                         in
                      failwith uu____14433
                    else
                      (let uu____14442 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____14442)
                | uu____14443 -> norm cfg env stack t2))

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
              let uu____14452 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14452 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14466  ->
                        let uu____14467 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14467);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14480  ->
                        let uu____14481 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14483 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14481 uu____14483);
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
                      | (UnivArgs (us',uu____14496))::stack1 ->
                          ((let uu____14505 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14505
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14513 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14513) us'
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
                      | uu____14549 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14552 ->
                          let uu____14555 =
                            let uu____14557 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14557
                             in
                          failwith uu____14555
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
                  let uu___1823_14585 = cfg  in
                  let uu____14586 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____14586;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1823_14585.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1823_14585.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1823_14585.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1823_14585.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1823_14585.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1823_14585.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1823_14585.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____14617,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14618;
                                    FStar_Syntax_Syntax.vars = uu____14619;_},uu____14620,uu____14621))::uu____14622
                     -> ()
                 | uu____14627 ->
                     let uu____14630 =
                       let uu____14632 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14632
                        in
                     failwith uu____14630);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____14641  ->
                      let uu____14642 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____14644 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____14642
                        uu____14644);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____14648 =
                    let uu____14649 = FStar_Syntax_Subst.compress head3  in
                    uu____14649.FStar_Syntax_Syntax.n  in
                  match uu____14648 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____14670 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____14670
                         in
                      let uu____14671 =
                        let uu____14680 =
                          FStar_All.pipe_right ed
                            FStar_Syntax_Util.get_bind_repr
                           in
                        FStar_All.pipe_right uu____14680 FStar_Util.must  in
                      (match uu____14671 with
                       | (uu____14695,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14705 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____14716 =
                                    let uu____14717 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14717.FStar_Syntax_Syntax.n  in
                                  match uu____14716 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____14723,uu____14724))
                                      ->
                                      let uu____14733 =
                                        let uu____14734 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____14734.FStar_Syntax_Syntax.n  in
                                      (match uu____14733 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____14740,msrc,uu____14742))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____14751 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____14751
                                       | uu____14752 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____14753 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____14754 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____14754 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___1895_14759 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___1895_14759.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___1895_14759.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___1895_14759.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___1895_14759.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___1895_14759.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____14760 = FStar_List.tl stack
                                        in
                                     let uu____14761 =
                                       let uu____14762 =
                                         let uu____14769 =
                                           let uu____14770 =
                                             let uu____14784 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____14784)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____14770
                                            in
                                         FStar_Syntax_Syntax.mk uu____14769
                                          in
                                       uu____14762
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____14760 uu____14761
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____14800 =
                                       let uu____14802 = is_return body  in
                                       match uu____14802 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____14807;
                                             FStar_Syntax_Syntax.vars =
                                               uu____14808;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____14811 -> false  in
                                     if uu____14800
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
                                          let uu____14835 =
                                            let uu____14842 =
                                              let uu____14843 =
                                                let uu____14862 =
                                                  let uu____14871 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____14871]  in
                                                (uu____14862, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____14843
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____14842
                                             in
                                          uu____14835
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____14910 =
                                            let uu____14911 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____14911.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14910 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____14917::uu____14918::[])
                                              ->
                                              let uu____14923 =
                                                let uu____14930 =
                                                  let uu____14931 =
                                                    let uu____14938 =
                                                      let uu____14939 =
                                                        let uu____14940 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____14940
                                                         in
                                                      let uu____14941 =
                                                        let uu____14944 =
                                                          let uu____14945 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____14945
                                                           in
                                                        [uu____14944]  in
                                                      uu____14939 ::
                                                        uu____14941
                                                       in
                                                    (bind1, uu____14938)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____14931
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____14930
                                                 in
                                              uu____14923
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____14948 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____14963 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____14963
                                          then
                                            let uu____14976 =
                                              let uu____14985 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____14985
                                               in
                                            let uu____14986 =
                                              let uu____14997 =
                                                let uu____15006 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____15006
                                                 in
                                              [uu____14997]  in
                                            uu____14976 :: uu____14986
                                          else []  in
                                        let reified =
                                          let args =
                                            let uu____15055 =
                                              FStar_Syntax_Util.is_layered ed
                                               in
                                            if uu____15055
                                            then
                                              let unit_args =
                                                let uu____15079 =
                                                  let uu____15080 =
                                                    let uu____15083 =
                                                      let uu____15084 =
                                                        FStar_All.pipe_right
                                                          ed
                                                          FStar_Syntax_Util.get_bind_vc_combinator
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____15084
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15083
                                                      FStar_Syntax_Subst.compress
                                                     in
                                                  uu____15080.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____15079 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (uu____15125::uu____15126::bs,uu____15128)
                                                    when
                                                    (FStar_List.length bs) >=
                                                      (Prims.of_int (2))
                                                    ->
                                                    let uu____15180 =
                                                      let uu____15189 =
                                                        FStar_All.pipe_right
                                                          bs
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs)
                                                                -
                                                                (Prims.of_int (2))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____15189
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____15180
                                                      (FStar_List.map
                                                         (fun uu____15320  ->
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.unit_const))
                                                | uu____15327 ->
                                                    let uu____15328 =
                                                      let uu____15334 =
                                                        let uu____15336 =
                                                          FStar_Ident.string_of_lid
                                                            ed.FStar_Syntax_Syntax.mname
                                                           in
                                                        let uu____15338 =
                                                          let uu____15340 =
                                                            let uu____15341 =
                                                              FStar_All.pipe_right
                                                                ed
                                                                FStar_Syntax_Util.get_bind_vc_combinator
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____15341
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____15340
                                                            FStar_Syntax_Print.term_to_string
                                                           in
                                                        FStar_Util.format2
                                                          "bind_wp for layered effect %s is not an arrow with >= 4 arguments (%s)"
                                                          uu____15336
                                                          uu____15338
                                                         in
                                                      (FStar_Errors.Fatal_UnexpectedEffect,
                                                        uu____15334)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____15328 rng
                                                 in
                                              let uu____15375 =
                                                FStar_Syntax_Syntax.as_arg
                                                  lb.FStar_Syntax_Syntax.lbtyp
                                                 in
                                              let uu____15384 =
                                                let uu____15395 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t
                                                   in
                                                let uu____15404 =
                                                  let uu____15415 =
                                                    let uu____15426 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head4
                                                       in
                                                    let uu____15435 =
                                                      let uu____15446 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          body2
                                                         in
                                                      [uu____15446]  in
                                                    uu____15426 ::
                                                      uu____15435
                                                     in
                                                  FStar_List.append unit_args
                                                    uu____15415
                                                   in
                                                uu____15395 :: uu____15404
                                                 in
                                              uu____15375 :: uu____15384
                                            else
                                              (let uu____15505 =
                                                 let uu____15516 =
                                                   FStar_Syntax_Syntax.as_arg
                                                     lb.FStar_Syntax_Syntax.lbtyp
                                                    in
                                                 let uu____15525 =
                                                   let uu____15536 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       t
                                                      in
                                                   [uu____15536]  in
                                                 uu____15516 :: uu____15525
                                                  in
                                               let uu____15569 =
                                                 let uu____15580 =
                                                   let uu____15591 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       FStar_Syntax_Syntax.tun
                                                      in
                                                   let uu____15600 =
                                                     let uu____15611 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         head4
                                                        in
                                                     let uu____15620 =
                                                       let uu____15631 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           FStar_Syntax_Syntax.tun
                                                          in
                                                       let uu____15640 =
                                                         let uu____15651 =
                                                           FStar_Syntax_Syntax.as_arg
                                                             body2
                                                            in
                                                         [uu____15651]  in
                                                       uu____15631 ::
                                                         uu____15640
                                                        in
                                                     uu____15611 ::
                                                       uu____15620
                                                      in
                                                   uu____15591 :: uu____15600
                                                    in
                                                 FStar_List.append
                                                   maybe_range_arg
                                                   uu____15580
                                                  in
                                               FStar_List.append uu____15505
                                                 uu____15569)
                                             in
                                          FStar_Syntax_Syntax.mk
                                            (FStar_Syntax_Syntax.Tm_app
                                               (bind_inst, args))
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____15732  ->
                                             let uu____15733 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____15735 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____15733 uu____15735);
                                        (let uu____15738 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____15738 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____15766 = FStar_Options.defensive ()  in
                        if uu____15766
                        then
                          let is_arg_impure uu____15781 =
                            match uu____15781 with
                            | (e,q) ->
                                let uu____15795 =
                                  let uu____15796 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____15796.FStar_Syntax_Syntax.n  in
                                (match uu____15795 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____15812 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____15812
                                 | uu____15814 -> false)
                             in
                          let uu____15816 =
                            let uu____15818 =
                              let uu____15829 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____15829 :: args  in
                            FStar_Util.for_some is_arg_impure uu____15818  in
                          (if uu____15816
                           then
                             let uu____15855 =
                               let uu____15861 =
                                 let uu____15863 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____15863
                                  in
                               (FStar_Errors.Warning_Defensive, uu____15861)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____15855
                           else ())
                        else ());
                       (let fallback1 uu____15876 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15880  ->
                               let uu____15881 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____15881 "");
                          (let uu____15885 = FStar_List.tl stack  in
                           let uu____15886 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____15885 uu____15886)
                           in
                        let fallback2 uu____15892 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15896  ->
                               let uu____15897 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____15897 "");
                          (let uu____15901 = FStar_List.tl stack  in
                           let uu____15902 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____15901 uu____15902)
                           in
                        let uu____15907 =
                          let uu____15908 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____15908.FStar_Syntax_Syntax.n  in
                        match uu____15907 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____15914 =
                              let uu____15916 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____15916  in
                            if uu____15914
                            then fallback1 ()
                            else
                              (let uu____15921 =
                                 let uu____15923 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____15923  in
                               if uu____15921
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____15940 =
                                      let uu____15945 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____15945 args
                                       in
                                    uu____15940 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____15946 = FStar_List.tl stack  in
                                  norm cfg env uu____15946 t1))
                        | uu____15947 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____15949) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____15973 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____15973  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____15977  ->
                            let uu____15978 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____15978);
                       (let uu____15981 = FStar_List.tl stack  in
                        norm cfg env uu____15981 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____16102  ->
                                match uu____16102 with
                                | (pat,wopt,tm) ->
                                    let uu____16150 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____16150)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____16182 = FStar_List.tl stack  in
                      norm cfg env uu____16182 tm
                  | uu____16183 -> fallback ()))

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
              (fun uu____16197  ->
                 let uu____16198 = FStar_Ident.string_of_lid msrc  in
                 let uu____16200 = FStar_Ident.string_of_lid mtgt  in
                 let uu____16202 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____16198
                   uu____16200 uu____16202);
            (let uu____16205 =
               ((FStar_Syntax_Util.is_pure_effect msrc) ||
                  (FStar_Syntax_Util.is_div_effect msrc))
                 &&
                 (let uu____16208 =
                    FStar_All.pipe_right mtgt
                      (FStar_TypeChecker_Env.is_layered_effect env)
                     in
                  Prims.op_Negation uu____16208)
                in
             if uu____16205
             then
               let ed =
                 let uu____16213 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____16213  in
               let uu____16214 =
                 let uu____16221 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr
                    in
                 FStar_All.pipe_right uu____16221 FStar_Util.must  in
               match uu____16214 with
               | (uu____16258,return_repr) ->
                   let return_inst =
                     let uu____16267 =
                       let uu____16268 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____16268.FStar_Syntax_Syntax.n  in
                     match uu____16267 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____16274::[]) ->
                         let uu____16279 =
                           let uu____16286 =
                             let uu____16287 =
                               let uu____16294 =
                                 let uu____16295 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____16295]  in
                               (return_tm, uu____16294)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____16287  in
                           FStar_Syntax_Syntax.mk uu____16286  in
                         uu____16279 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____16298 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let args =
                     let uu____16313 = FStar_Syntax_Util.is_layered ed  in
                     if uu____16313
                     then
                       let unit_args =
                         let uu____16337 =
                           let uu____16338 =
                             let uu____16341 =
                               let uu____16342 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_return_vc_combinator
                                  in
                               FStar_All.pipe_right uu____16342
                                 FStar_Pervasives_Native.snd
                                in
                             FStar_All.pipe_right uu____16341
                               FStar_Syntax_Subst.compress
                              in
                           uu____16338.FStar_Syntax_Syntax.n  in
                         match uu____16337 with
                         | FStar_Syntax_Syntax.Tm_arrow
                             (uu____16375::bs,uu____16377) when
                             (FStar_List.length bs) >= Prims.int_one ->
                             let uu____16417 =
                               let uu____16426 =
                                 FStar_All.pipe_right bs
                                   (FStar_List.splitAt
                                      ((FStar_List.length bs) - Prims.int_one))
                                  in
                               FStar_All.pipe_right uu____16426
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_All.pipe_right uu____16417
                               (FStar_List.map
                                  (fun uu____16557  ->
                                     FStar_Syntax_Syntax.as_arg
                                       FStar_Syntax_Syntax.unit_const))
                         | uu____16564 ->
                             let uu____16565 =
                               let uu____16571 =
                                 let uu____16573 =
                                   FStar_Ident.string_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 let uu____16575 =
                                   let uu____16577 =
                                     let uu____16578 =
                                       FStar_All.pipe_right ed
                                         FStar_Syntax_Util.get_return_vc_combinator
                                        in
                                     FStar_All.pipe_right uu____16578
                                       FStar_Pervasives_Native.snd
                                      in
                                   FStar_All.pipe_right uu____16577
                                     FStar_Syntax_Print.term_to_string
                                    in
                                 FStar_Util.format2
                                   "ret_wp for layered effect %s is not an arrow with >= 2 binders (%s)"
                                   uu____16573 uu____16575
                                  in
                               (FStar_Errors.Fatal_UnexpectedEffect,
                                 uu____16571)
                                in
                             FStar_Errors.raise_error uu____16565
                               e.FStar_Syntax_Syntax.pos
                          in
                       let uu____16620 = FStar_Syntax_Syntax.as_arg t  in
                       let uu____16629 =
                         let uu____16640 =
                           let uu____16651 = FStar_Syntax_Syntax.as_arg e  in
                           [uu____16651]  in
                         FStar_List.append unit_args uu____16640  in
                       uu____16620 :: uu____16629
                     else
                       (let uu____16694 = FStar_Syntax_Syntax.as_arg t  in
                        let uu____16703 =
                          let uu____16714 = FStar_Syntax_Syntax.as_arg e  in
                          [uu____16714]  in
                        uu____16694 :: uu____16703)
                      in
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_app (return_inst, args))
                     FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
             else
               (let uu____16761 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____16761 with
                | FStar_Pervasives_Native.None  ->
                    let uu____16764 =
                      let uu____16766 = FStar_Ident.text_of_lid msrc  in
                      let uu____16768 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____16766 uu____16768
                       in
                    failwith uu____16764
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16771;
                      FStar_TypeChecker_Env.mtarget = uu____16772;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16773;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____16793 =
                      let uu____16795 = FStar_Ident.text_of_lid msrc  in
                      let uu____16797 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____16795 uu____16797
                       in
                    failwith uu____16793
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16800;
                      FStar_TypeChecker_Env.mtarget = uu____16801;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16802;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let e1 =
                      let uu____16833 =
                        FStar_TypeChecker_Env.is_reifiable_effect env msrc
                         in
                      if uu____16833
                      then FStar_Syntax_Util.mk_reify e
                      else
                        (let uu____16838 =
                           let uu____16845 =
                             let uu____16846 =
                               let uu____16865 =
                                 let uu____16874 =
                                   FStar_Syntax_Syntax.null_binder
                                     FStar_Syntax_Syntax.t_unit
                                    in
                                 [uu____16874]  in
                               (uu____16865, e,
                                 (FStar_Pervasives_Native.Some
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        msrc;
                                      FStar_Syntax_Syntax.residual_typ =
                                        (FStar_Pervasives_Native.Some t);
                                      FStar_Syntax_Syntax.residual_flags = []
                                    }))
                                in
                             FStar_Syntax_Syntax.Tm_abs uu____16846  in
                           FStar_Syntax_Syntax.mk uu____16845  in
                         uu____16838 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos)
                       in
                    let uu____16907 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    lift uu____16907 t e1))

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
                (fun uu____16977  ->
                   match uu____16977 with
                   | (a,imp) ->
                       let uu____16996 = norm cfg env [] a  in
                       (uu____16996, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____17006  ->
             let uu____17007 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____17009 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements\n"
               uu____17007 uu____17009);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17035 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17038  -> FStar_Pervasives_Native.Some _17038)
                     uu____17035
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2071_17039 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2071_17039.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2071_17039.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____17061 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _17064  -> FStar_Pervasives_Native.Some _17064)
                     uu____17061
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2082_17065 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2082_17065.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2082_17065.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____17110  ->
                      match uu____17110 with
                      | (a,i) ->
                          let uu____17130 = norm cfg env [] a  in
                          (uu____17130, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___14_17152  ->
                       match uu___14_17152 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____17156 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____17156
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2099_17164 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2101_17167 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2101_17167.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2099_17164.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2099_17164.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____17171 = b  in
        match uu____17171 with
        | (x,imp) ->
            let x1 =
              let uu___2109_17179 = x  in
              let uu____17180 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2109_17179.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2109_17179.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____17180
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____17191 =
                    let uu____17192 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____17192  in
                  FStar_Pervasives_Native.Some uu____17191
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____17203 =
          FStar_List.fold_left
            (fun uu____17237  ->
               fun b  ->
                 match uu____17237 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____17203 with | (nbs,uu____17317) -> FStar_List.rev nbs

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
            let uu____17349 =
              let uu___2134_17350 = rc  in
              let uu____17351 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2134_17350.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____17351;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2134_17350.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____17349
        | uu____17360 -> lopt

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
            (let uu____17370 = FStar_Syntax_Print.term_to_string tm  in
             let uu____17372 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____17370 uu____17372)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___15_17384  ->
      match uu___15_17384 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____17397 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____17397 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____17401 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____17401)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____17409 = norm_cb cfg  in
            reduce_primops uu____17409 cfg env tm  in
          let uu____17414 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____17414
          then tm1
          else
            (let w t =
               let uu___2162_17433 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2162_17433.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2162_17433.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____17445 =
                 let uu____17446 = FStar_Syntax_Util.unmeta t  in
                 uu____17446.FStar_Syntax_Syntax.n  in
               match uu____17445 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____17458 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____17522)::args1,(bv,uu____17525)::bs1) ->
                   let uu____17579 =
                     let uu____17580 = FStar_Syntax_Subst.compress t  in
                     uu____17580.FStar_Syntax_Syntax.n  in
                   (match uu____17579 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____17585 -> false)
               | ([],[]) -> true
               | (uu____17616,uu____17617) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17668 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17670 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____17668
                    uu____17670)
               else ();
               (let uu____17675 = FStar_Syntax_Util.head_and_args' t  in
                match uu____17675 with
                | (hd1,args) ->
                    let uu____17714 =
                      let uu____17715 = FStar_Syntax_Subst.compress hd1  in
                      uu____17715.FStar_Syntax_Syntax.n  in
                    (match uu____17714 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____17723 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____17725 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____17727 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____17723 uu____17725 uu____17727)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____17732 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17750 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17752 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17750
                    uu____17752)
               else ();
               (let uu____17757 = FStar_Syntax_Util.is_squash t  in
                match uu____17757 with
                | FStar_Pervasives_Native.Some (uu____17768,t') ->
                    is_applied bs t'
                | uu____17780 ->
                    let uu____17789 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____17789 with
                     | FStar_Pervasives_Native.Some (uu____17800,t') ->
                         is_applied bs t'
                     | uu____17812 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____17836 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17836 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17843)::(q,uu____17845)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17888 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____17890 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17888 uu____17890)
                    else ();
                    (let uu____17895 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____17895 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17900 =
                           let uu____17901 = FStar_Syntax_Subst.compress p
                              in
                           uu____17901.FStar_Syntax_Syntax.n  in
                         (match uu____17900 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____17912 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17912))
                          | uu____17915 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____17918)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____17943 =
                           let uu____17944 = FStar_Syntax_Subst.compress p1
                              in
                           uu____17944.FStar_Syntax_Syntax.n  in
                         (match uu____17943 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____17955 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17955))
                          | uu____17958 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____17962 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____17962 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____17967 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____17967 with
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
                                     let uu____17981 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17981))
                               | uu____17984 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____17989)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____18014 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____18014 with
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
                                     let uu____18028 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____18028))
                               | uu____18031 -> FStar_Pervasives_Native.None)
                          | uu____18034 -> FStar_Pervasives_Native.None)
                     | uu____18037 -> FStar_Pervasives_Native.None))
               | uu____18040 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____18053 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____18053 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____18059)::[],uu____18060,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____18080 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____18082 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____18080
                         uu____18082)
                    else ();
                    is_quantified_const bv phi')
               | uu____18087 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____18102 =
                 let uu____18103 = FStar_Syntax_Subst.compress phi  in
                 uu____18103.FStar_Syntax_Syntax.n  in
               match uu____18102 with
               | FStar_Syntax_Syntax.Tm_match (uu____18109,br::brs) ->
                   let uu____18176 = br  in
                   (match uu____18176 with
                    | (uu____18194,uu____18195,e) ->
                        let r =
                          let uu____18217 = simp_t e  in
                          match uu____18217 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____18229 =
                                FStar_List.for_all
                                  (fun uu____18248  ->
                                     match uu____18248 with
                                     | (uu____18262,uu____18263,e') ->
                                         let uu____18277 = simp_t e'  in
                                         uu____18277 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____18229
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____18293 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____18303 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____18303
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____18341 =
                 match uu____18341 with
                 | (t1,q) ->
                     let uu____18362 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____18362 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____18394 -> (t1, q))
                  in
               let uu____18407 = FStar_Syntax_Util.head_and_args t  in
               match uu____18407 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____18487 =
                 let uu____18488 = FStar_Syntax_Util.unmeta ty  in
                 uu____18488.FStar_Syntax_Syntax.n  in
               match uu____18487 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____18493) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____18498,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____18522 -> false  in
             let simplify1 arg =
               let uu____18555 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____18555, arg)  in
             let uu____18570 = is_forall_const tm1  in
             match uu____18570 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____18576 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____18578 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____18576
                       uu____18578)
                  else ();
                  (let uu____18583 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____18583))
             | FStar_Pervasives_Native.None  ->
                 let uu____18584 =
                   let uu____18585 = FStar_Syntax_Subst.compress tm1  in
                   uu____18585.FStar_Syntax_Syntax.n  in
                 (match uu____18584 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____18589;
                              FStar_Syntax_Syntax.vars = uu____18590;_},uu____18591);
                         FStar_Syntax_Syntax.pos = uu____18592;
                         FStar_Syntax_Syntax.vars = uu____18593;_},args)
                      ->
                      let uu____18623 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____18623
                      then
                        let uu____18626 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____18626 with
                         | (FStar_Pervasives_Native.Some (true ),uu____18684)::
                             (uu____18685,(arg,uu____18687))::[] ->
                             maybe_auto_squash arg
                         | (uu____18760,(arg,uu____18762))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18763)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18836)::uu____18837::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18907::(FStar_Pervasives_Native.Some (false
                                         ),uu____18908)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18978 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18996 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18996
                         then
                           let uu____18999 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18999 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____19057)::uu____19058::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____19128::(FStar_Pervasives_Native.Some (true
                                           ),uu____19129)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____19199)::(uu____19200,(arg,uu____19202))::[]
                               -> maybe_auto_squash arg
                           | (uu____19275,(arg,uu____19277))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____19278)::[]
                               -> maybe_auto_squash arg
                           | uu____19351 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____19369 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____19369
                            then
                              let uu____19372 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____19372 with
                              | uu____19430::(FStar_Pervasives_Native.Some
                                              (true ),uu____19431)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____19501)::uu____19502::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____19572)::(uu____19573,(arg,uu____19575))::[]
                                  -> maybe_auto_squash arg
                              | (uu____19648,(p,uu____19650))::(uu____19651,
                                                                (q,uu____19653))::[]
                                  ->
                                  let uu____19725 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____19725
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____19730 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19748 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19748
                               then
                                 let uu____19751 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19751 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19809)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19810)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19884)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19885)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19959)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19960)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20034)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____20035)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____20109,(arg,uu____20111))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____20112)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____20185)::(uu____20186,(arg,uu____20188))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____20261,(arg,uu____20263))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____20264)::[]
                                     ->
                                     let uu____20337 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20337
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____20338)::(uu____20339,(arg,uu____20341))::[]
                                     ->
                                     let uu____20414 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____20414
                                 | (uu____20415,(p,uu____20417))::(uu____20418,
                                                                   (q,uu____20420))::[]
                                     ->
                                     let uu____20492 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____20492
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____20497 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____20515 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____20515
                                  then
                                    let uu____20518 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____20518 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____20576)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____20620)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____20664 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____20682 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____20682
                                     then
                                       match args with
                                       | (t,uu____20686)::[] ->
                                           let uu____20711 =
                                             let uu____20712 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20712.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20711 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20715::[],body,uu____20717)
                                                ->
                                                let uu____20752 = simp_t body
                                                   in
                                                (match uu____20752 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20758 -> tm1)
                                            | uu____20762 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20764))::(t,uu____20766)::[]
                                           ->
                                           let uu____20806 =
                                             let uu____20807 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20807.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20806 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20810::[],body,uu____20812)
                                                ->
                                                let uu____20847 = simp_t body
                                                   in
                                                (match uu____20847 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20855 -> tm1)
                                            | uu____20859 -> tm1)
                                       | uu____20860 -> tm1
                                     else
                                       (let uu____20873 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20873
                                        then
                                          match args with
                                          | (t,uu____20877)::[] ->
                                              let uu____20902 =
                                                let uu____20903 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20903.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20902 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20906::[],body,uu____20908)
                                                   ->
                                                   let uu____20943 =
                                                     simp_t body  in
                                                   (match uu____20943 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20949 -> tm1)
                                               | uu____20953 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20955))::(t,uu____20957)::[]
                                              ->
                                              let uu____20997 =
                                                let uu____20998 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20998.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20997 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____21001::[],body,uu____21003)
                                                   ->
                                                   let uu____21038 =
                                                     simp_t body  in
                                                   (match uu____21038 with
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
                                                    | uu____21046 -> tm1)
                                               | uu____21050 -> tm1)
                                          | uu____21051 -> tm1
                                        else
                                          (let uu____21064 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____21064
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21067;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21068;_},uu____21069)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____21095;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____21096;_},uu____21097)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____21123 -> tm1
                                           else
                                             (let uu____21136 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____21136
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____21150 =
                                                    let uu____21151 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____21151.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____21150 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____21162 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____21176 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____21176
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____21215 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____21215
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____21221 =
                                                         let uu____21222 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____21222.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____21221 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____21225 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____21233 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____21233
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____21242
                                                                  =
                                                                  let uu____21243
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____21243.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____21242
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____21249)
                                                                    -> hd1
                                                                | uu____21274
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____21278
                                                                =
                                                                let uu____21289
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____21289]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____21278)
                                                       | uu____21322 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____21327 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____21327 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____21347 ->
                                                     let uu____21356 =
                                                       let uu____21363 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____21363 cfg env
                                                        in
                                                     uu____21356 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____21369;
                         FStar_Syntax_Syntax.vars = uu____21370;_},args)
                      ->
                      let uu____21396 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____21396
                      then
                        let uu____21399 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____21399 with
                         | (FStar_Pervasives_Native.Some (true ),uu____21457)::
                             (uu____21458,(arg,uu____21460))::[] ->
                             maybe_auto_squash arg
                         | (uu____21533,(arg,uu____21535))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____21536)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____21609)::uu____21610::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____21680::(FStar_Pervasives_Native.Some (false
                                         ),uu____21681)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21751 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21769 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21769
                         then
                           let uu____21772 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21772 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21830)::uu____21831::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21901::(FStar_Pervasives_Native.Some (true
                                           ),uu____21902)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21972)::(uu____21973,(arg,uu____21975))::[]
                               -> maybe_auto_squash arg
                           | (uu____22048,(arg,uu____22050))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____22051)::[]
                               -> maybe_auto_squash arg
                           | uu____22124 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____22142 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____22142
                            then
                              let uu____22145 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____22145 with
                              | uu____22203::(FStar_Pervasives_Native.Some
                                              (true ),uu____22204)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____22274)::uu____22275::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____22345)::(uu____22346,(arg,uu____22348))::[]
                                  -> maybe_auto_squash arg
                              | (uu____22421,(p,uu____22423))::(uu____22424,
                                                                (q,uu____22426))::[]
                                  ->
                                  let uu____22498 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____22498
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____22503 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____22521 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____22521
                               then
                                 let uu____22524 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____22524 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22582)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22583)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22657)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22658)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22732)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____22733)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22807)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22808)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22882,(arg,uu____22884))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22885)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22958)::(uu____22959,(arg,uu____22961))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____23034,(arg,uu____23036))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____23037)::[]
                                     ->
                                     let uu____23110 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23110
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____23111)::(uu____23112,(arg,uu____23114))::[]
                                     ->
                                     let uu____23187 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____23187
                                 | (uu____23188,(p,uu____23190))::(uu____23191,
                                                                   (q,uu____23193))::[]
                                     ->
                                     let uu____23265 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____23265
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____23270 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____23288 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____23288
                                  then
                                    let uu____23291 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____23291 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____23349)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____23393)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____23437 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____23455 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____23455
                                     then
                                       match args with
                                       | (t,uu____23459)::[] ->
                                           let uu____23484 =
                                             let uu____23485 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23485.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23484 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23488::[],body,uu____23490)
                                                ->
                                                let uu____23525 = simp_t body
                                                   in
                                                (match uu____23525 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____23531 -> tm1)
                                            | uu____23535 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____23537))::(t,uu____23539)::[]
                                           ->
                                           let uu____23579 =
                                             let uu____23580 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____23580.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____23579 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____23583::[],body,uu____23585)
                                                ->
                                                let uu____23620 = simp_t body
                                                   in
                                                (match uu____23620 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____23628 -> tm1)
                                            | uu____23632 -> tm1)
                                       | uu____23633 -> tm1
                                     else
                                       (let uu____23646 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____23646
                                        then
                                          match args with
                                          | (t,uu____23650)::[] ->
                                              let uu____23675 =
                                                let uu____23676 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23676.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23675 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23679::[],body,uu____23681)
                                                   ->
                                                   let uu____23716 =
                                                     simp_t body  in
                                                   (match uu____23716 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____23722 -> tm1)
                                               | uu____23726 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____23728))::(t,uu____23730)::[]
                                              ->
                                              let uu____23770 =
                                                let uu____23771 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23771.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23770 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23774::[],body,uu____23776)
                                                   ->
                                                   let uu____23811 =
                                                     simp_t body  in
                                                   (match uu____23811 with
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
                                                    | uu____23819 -> tm1)
                                               | uu____23823 -> tm1)
                                          | uu____23824 -> tm1
                                        else
                                          (let uu____23837 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____23837
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23840;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23841;_},uu____23842)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23868;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23869;_},uu____23870)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____23896 -> tm1
                                           else
                                             (let uu____23909 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____23909
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____23923 =
                                                    let uu____23924 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____23924.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____23923 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____23935 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____23949 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____23949
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____23984 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____23984
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____23990 =
                                                         let uu____23991 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____23991.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____23990 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____23994 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____24002 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____24002
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____24011
                                                                  =
                                                                  let uu____24012
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____24012.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____24011
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____24018)
                                                                    -> hd1
                                                                | uu____24043
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____24047
                                                                =
                                                                let uu____24058
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____24058]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____24047)
                                                       | uu____24091 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____24096 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____24096 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____24116 ->
                                                     let uu____24125 =
                                                       let uu____24132 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____24132 cfg env
                                                        in
                                                     uu____24125 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____24143 = simp_t t  in
                      (match uu____24143 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____24152 ->
                      let uu____24175 = is_const_match tm1  in
                      (match uu____24175 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____24184 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____24194  ->
               (let uu____24196 = FStar_Syntax_Print.tag_of_term t  in
                let uu____24198 = FStar_Syntax_Print.term_to_string t  in
                let uu____24200 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____24208 =
                  let uu____24210 =
                    let uu____24213 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____24213
                     in
                  stack_to_string uu____24210  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____24196 uu____24198 uu____24200 uu____24208);
               (let uu____24238 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____24238
                then
                  let uu____24242 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____24242 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____24249 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____24251 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____24253 =
                          let uu____24255 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____24255
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____24249
                          uu____24251 uu____24253);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____24277 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____24285)::uu____24286 -> true
                | uu____24296 -> false)
              in
           if uu____24277
           then
             let uu____24299 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____24299 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____24313 =
                        let uu____24315 =
                          let uu____24317 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____24317  in
                        FStar_Util.string_of_int uu____24315  in
                      let uu____24324 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____24326 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____24313 uu____24324 uu____24326)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____24335,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24364  ->
                        let uu____24365 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____24365);
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
                  let uu____24408 =
                    let uu___2791_24409 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2791_24409.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2791_24409.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____24408
              | (Arg (Univ uu____24412,uu____24413,uu____24414))::uu____24415
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____24419,uu____24420))::uu____24421 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____24437,uu____24438),aq,r))::stack1
                  when
                  let uu____24490 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____24490 ->
                  let t2 =
                    let uu____24494 =
                      let uu____24499 =
                        let uu____24500 = closure_as_term cfg env_arg tm  in
                        (uu____24500, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____24499  in
                    uu____24494 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____24510),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____24565  ->
                        let uu____24566 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____24566);
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
                     (let uu____24586 = FStar_ST.op_Bang m  in
                      match uu____24586 with
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
                      | FStar_Pervasives_Native.Some (uu____24674,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____24730 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____24735  ->
                         let uu____24736 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____24736);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____24746 =
                    let uu____24747 = FStar_Syntax_Subst.compress t1  in
                    uu____24747.FStar_Syntax_Syntax.n  in
                  (match uu____24746 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____24775 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____24775  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____24779  ->
                             let uu____24780 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____24780);
                        (let uu____24783 = FStar_List.tl stack  in
                         norm cfg env1 uu____24783 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____24784);
                          FStar_Syntax_Syntax.pos = uu____24785;
                          FStar_Syntax_Syntax.vars = uu____24786;_},(e,uu____24788)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____24827 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____24844 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____24844 with
                        | (hd1,args) ->
                            let uu____24887 =
                              let uu____24888 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____24888.FStar_Syntax_Syntax.n  in
                            (match uu____24887 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____24892 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____24892 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____24895;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____24896;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____24897;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____24899;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____24900;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____24901;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____24902;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____24938 -> fallback " (3)" ())
                             | uu____24942 -> fallback " (4)" ()))
                   | uu____24944 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____24970  ->
                        let uu____24971 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____24971);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____24982 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____24987  ->
                           let uu____24988 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____24990 =
                             let uu____24992 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____25022  ->
                                       match uu____25022 with
                                       | (p,uu____25033,uu____25034) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____24992
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____24988 uu____24990);
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
                                (fun uu___16_25056  ->
                                   match uu___16_25056 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____25060 -> false))
                            in
                         let steps =
                           let uu___2959_25063 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___2959_25063.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___2962_25070 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___2962_25070.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___2962_25070.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___2962_25070.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___2962_25070.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___2962_25070.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___2962_25070.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____25145 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____25176 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____25265  ->
                                       fun uu____25266  ->
                                         match (uu____25265, uu____25266)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____25416 =
                                               norm_pat env3 p1  in
                                             (match uu____25416 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____25176 with
                              | (pats1,env3) ->
                                  ((let uu___2990_25586 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___2990_25586.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___2994_25607 = x  in
                               let uu____25608 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2994_25607.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2994_25607.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25608
                               }  in
                             ((let uu___2997_25622 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___2997_25622.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___3001_25633 = x  in
                               let uu____25634 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3001_25633.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3001_25633.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25634
                               }  in
                             ((let uu___3004_25648 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3004_25648.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3010_25664 = x  in
                               let uu____25665 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3010_25664.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3010_25664.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____25665
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3014_25680 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3014_25680.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____25724 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____25754 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____25754 with
                                     | (p,wopt,e) ->
                                         let uu____25774 = norm_pat env1 p
                                            in
                                         (match uu____25774 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____25829 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____25829
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____25846 =
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
                         if uu____25846
                         then
                           norm
                             (let uu___3033_25853 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3035_25856 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3035_25856.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3033_25853.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3033_25853.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3033_25853.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3033_25853.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3033_25853.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3033_25853.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3033_25853.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3033_25853.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____25860 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____25860)
                       in
                    let rec is_cons head1 =
                      let uu____25886 =
                        let uu____25887 = FStar_Syntax_Subst.compress head1
                           in
                        uu____25887.FStar_Syntax_Syntax.n  in
                      match uu____25886 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____25892) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____25897 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____25899;
                            FStar_Syntax_Syntax.fv_delta = uu____25900;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____25902;
                            FStar_Syntax_Syntax.fv_delta = uu____25903;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____25904);_}
                          -> true
                      | uu____25912 -> false  in
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
                      let uu____26081 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____26081 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____26178 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____26220 ->
                                    let uu____26221 =
                                      let uu____26223 = is_cons head1  in
                                      Prims.op_Negation uu____26223  in
                                    FStar_Util.Inr uu____26221)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____26252 =
                                 let uu____26253 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____26253.FStar_Syntax_Syntax.n  in
                               (match uu____26252 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____26272 ->
                                    let uu____26273 =
                                      let uu____26275 = is_cons head1  in
                                      Prims.op_Negation uu____26275  in
                                    FStar_Util.Inr uu____26273))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____26366)::rest_a,(p1,uu____26369)::rest_p)
                          ->
                          let uu____26428 = matches_pat t2 p1  in
                          (match uu____26428 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____26481 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____26604 = matches_pat scrutinee1 p1  in
                          (match uu____26604 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____26650  ->
                                     let uu____26651 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____26653 =
                                       let uu____26655 =
                                         FStar_List.map
                                           (fun uu____26667  ->
                                              match uu____26667 with
                                              | (uu____26673,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____26655
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____26651 uu____26653);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____26709  ->
                                          match uu____26709 with
                                          | (bv,t2) ->
                                              let uu____26732 =
                                                let uu____26739 =
                                                  let uu____26742 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____26742
                                                   in
                                                let uu____26743 =
                                                  let uu____26744 =
                                                    let uu____26776 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____26776,
                                                      false)
                                                     in
                                                  Clos uu____26744  in
                                                (uu____26739, uu____26743)
                                                 in
                                              uu____26732 :: env2) env1 s
                                    in
                                 let uu____26869 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____26869)))
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
            (fun uu____26902  ->
               let uu____26903 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____26903);
          (let uu____26906 = is_nbe_request s  in
           if uu____26906
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____26912  ->
                   let uu____26913 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____26913);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____26919  ->
                   let uu____26920 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26920);
              (let uu____26923 =
                 FStar_Util.record_time (fun uu____26930  -> nbe_eval c s t)
                  in
               match uu____26923 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26939  ->
                         let uu____26940 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26942 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26940 uu____26942);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____26950  ->
                   let uu____26951 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____26951);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____26957  ->
                   let uu____26958 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26958);
              (let uu____26961 =
                 FStar_Util.record_time (fun uu____26968  -> norm c [] [] t)
                  in
               match uu____26961 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26983  ->
                         let uu____26984 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26986 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26984 uu____26986);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27005 =
          let uu____27009 =
            let uu____27011 = FStar_TypeChecker_Env.current_module e  in
            FStar_Ident.string_of_lid uu____27011  in
          FStar_Pervasives_Native.Some uu____27009  in
        FStar_Profiling.profile
          (fun uu____27014  -> normalize_with_primitive_steps [] s e t)
          uu____27005 "FStar.TypeChecker.Normalize"
  
let (normalize_comp :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____27032 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____27032 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____27050 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____27050 [] u
  
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
        let uu____27076 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____27076  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____27083 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3192_27102 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3192_27102.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3192_27102.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____27109 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____27109
          then
            let ct1 =
              let uu____27113 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____27113 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____27120 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____27120
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3202_27127 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3202_27127.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3202_27127.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3202_27127.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___3206_27129 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3206_27129.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3206_27129.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3206_27129.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3206_27129.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3209_27130 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3209_27130.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3209_27130.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____27133 -> c
  
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
        let uu____27153 = norm cfg [] [] t  in
        FStar_TypeChecker_Env.non_informative env uu____27153  in
      let uu____27160 =
        (FStar_Syntax_Util.is_ghost_effect
           lc.FStar_TypeChecker_Common.eff_name)
          && (non_info lc.FStar_TypeChecker_Common.res_typ)
         in
      if uu____27160
      then
        let uu____27163 =
          downgrade_ghost_effect_name lc.FStar_TypeChecker_Common.eff_name
           in
        match uu____27163 with
        | FStar_Pervasives_Native.Some pure_eff ->
            let uu___3220_27167 =
              FStar_TypeChecker_Common.apply_lcomp (ghost_to_pure env)
                (fun g  -> g) lc
               in
            {
              FStar_TypeChecker_Common.eff_name = pure_eff;
              FStar_TypeChecker_Common.res_typ =
                (uu___3220_27167.FStar_TypeChecker_Common.res_typ);
              FStar_TypeChecker_Common.cflags =
                (uu___3220_27167.FStar_TypeChecker_Common.cflags);
              FStar_TypeChecker_Common.comp_thunk =
                (uu___3220_27167.FStar_TypeChecker_Common.comp_thunk)
            }
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3227_27186  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3226_27189 ->
            ((let uu____27191 =
                let uu____27197 =
                  let uu____27199 = FStar_Util.message_of_exn uu___3226_27189
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27199
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27197)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____27191);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3237_27218  ->
             match () with
             | () ->
                 let uu____27219 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____27219 [] c) ()
        with
        | uu___3236_27228 ->
            ((let uu____27230 =
                let uu____27236 =
                  let uu____27238 = FStar_Util.message_of_exn uu___3236_27228
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____27238
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____27236)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____27230);
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
                   let uu____27287 =
                     let uu____27288 =
                       let uu____27295 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____27295)  in
                     FStar_Syntax_Syntax.Tm_refine uu____27288  in
                   mk uu____27287 t01.FStar_Syntax_Syntax.pos
               | uu____27300 -> t2)
          | uu____27301 -> t2  in
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
        let uu____27395 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____27395 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____27432 ->
                 let uu____27441 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____27441 with
                  | (actuals,uu____27451,uu____27452) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____27472 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____27472 with
                         | (binders,args) ->
                             let uu____27483 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____27483
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
      | uu____27498 ->
          let uu____27499 = FStar_Syntax_Util.head_and_args t  in
          (match uu____27499 with
           | (head1,args) ->
               let uu____27542 =
                 let uu____27543 = FStar_Syntax_Subst.compress head1  in
                 uu____27543.FStar_Syntax_Syntax.n  in
               (match uu____27542 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____27564 =
                      let uu____27579 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____27579  in
                    (match uu____27564 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____27619 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3307_27627 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3307_27627.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3307_27627.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3307_27627.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3307_27627.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3307_27627.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3307_27627.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3307_27627.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3307_27627.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3307_27627.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3307_27627.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3307_27627.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3307_27627.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3307_27627.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3307_27627.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3307_27627.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3307_27627.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3307_27627.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3307_27627.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3307_27627.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3307_27627.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3307_27627.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3307_27627.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3307_27627.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3307_27627.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3307_27627.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3307_27627.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3307_27627.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3307_27627.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3307_27627.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3307_27627.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3307_27627.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3307_27627.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3307_27627.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___3307_27627.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3307_27627.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3307_27627.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3307_27627.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3307_27627.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3307_27627.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3307_27627.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3307_27627.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___3307_27627.FStar_TypeChecker_Env.erasable_types_tab)
                                 }) t
                               in
                            match uu____27619 with
                            | (uu____27630,ty,uu____27632) ->
                                eta_expand_with_type env t ty))
                | uu____27633 ->
                    let uu____27634 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3314_27642 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3314_27642.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3314_27642.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3314_27642.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3314_27642.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3314_27642.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3314_27642.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3314_27642.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3314_27642.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3314_27642.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3314_27642.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3314_27642.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3314_27642.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3314_27642.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3314_27642.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3314_27642.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3314_27642.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3314_27642.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3314_27642.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3314_27642.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3314_27642.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3314_27642.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3314_27642.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3314_27642.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3314_27642.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3314_27642.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3314_27642.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3314_27642.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3314_27642.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3314_27642.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3314_27642.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3314_27642.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3314_27642.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3314_27642.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.mpreprocess =
                             (uu___3314_27642.FStar_TypeChecker_Env.mpreprocess);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3314_27642.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3314_27642.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3314_27642.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3314_27642.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3314_27642.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3314_27642.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3314_27642.FStar_TypeChecker_Env.strict_args_tab);
                           FStar_TypeChecker_Env.erasable_types_tab =
                             (uu___3314_27642.FStar_TypeChecker_Env.erasable_types_tab)
                         }) t
                       in
                    (match uu____27634 with
                     | (uu____27645,ty,uu____27647) ->
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
      let uu___3326_27729 = x  in
      let uu____27730 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3326_27729.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3326_27729.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27730
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27733 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27757 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27758 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27759 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27760 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27767 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27768 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27769 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3352_27803 = rc  in
          let uu____27804 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____27813 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3352_27803.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27804;
            FStar_Syntax_Syntax.residual_flags = uu____27813
          }  in
        let uu____27816 =
          let uu____27817 =
            let uu____27836 = elim_delayed_subst_binders bs  in
            let uu____27845 = elim_delayed_subst_term t2  in
            let uu____27848 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____27836, uu____27845, uu____27848)  in
          FStar_Syntax_Syntax.Tm_abs uu____27817  in
        mk1 uu____27816
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____27885 =
          let uu____27886 =
            let uu____27901 = elim_delayed_subst_binders bs  in
            let uu____27910 = elim_delayed_subst_comp c  in
            (uu____27901, uu____27910)  in
          FStar_Syntax_Syntax.Tm_arrow uu____27886  in
        mk1 uu____27885
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____27929 =
          let uu____27930 =
            let uu____27937 = elim_bv bv  in
            let uu____27938 = elim_delayed_subst_term phi  in
            (uu____27937, uu____27938)  in
          FStar_Syntax_Syntax.Tm_refine uu____27930  in
        mk1 uu____27929
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____27969 =
          let uu____27970 =
            let uu____27987 = elim_delayed_subst_term t2  in
            let uu____27990 = elim_delayed_subst_args args  in
            (uu____27987, uu____27990)  in
          FStar_Syntax_Syntax.Tm_app uu____27970  in
        mk1 uu____27969
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3374_28062 = p  in
              let uu____28063 =
                let uu____28064 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____28064  in
              {
                FStar_Syntax_Syntax.v = uu____28063;
                FStar_Syntax_Syntax.p =
                  (uu___3374_28062.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3378_28066 = p  in
              let uu____28067 =
                let uu____28068 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____28068  in
              {
                FStar_Syntax_Syntax.v = uu____28067;
                FStar_Syntax_Syntax.p =
                  (uu___3378_28066.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3384_28075 = p  in
              let uu____28076 =
                let uu____28077 =
                  let uu____28084 = elim_bv x  in
                  let uu____28085 = elim_delayed_subst_term t0  in
                  (uu____28084, uu____28085)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____28077  in
              {
                FStar_Syntax_Syntax.v = uu____28076;
                FStar_Syntax_Syntax.p =
                  (uu___3384_28075.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3390_28110 = p  in
              let uu____28111 =
                let uu____28112 =
                  let uu____28126 =
                    FStar_List.map
                      (fun uu____28152  ->
                         match uu____28152 with
                         | (x,b) ->
                             let uu____28169 = elim_pat x  in
                             (uu____28169, b)) pats
                     in
                  (fv, uu____28126)  in
                FStar_Syntax_Syntax.Pat_cons uu____28112  in
              {
                FStar_Syntax_Syntax.v = uu____28111;
                FStar_Syntax_Syntax.p =
                  (uu___3390_28110.FStar_Syntax_Syntax.p)
              }
          | uu____28184 -> p  in
        let elim_branch uu____28208 =
          match uu____28208 with
          | (pat,wopt,t3) ->
              let uu____28234 = elim_pat pat  in
              let uu____28237 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____28240 = elim_delayed_subst_term t3  in
              (uu____28234, uu____28237, uu____28240)
           in
        let uu____28245 =
          let uu____28246 =
            let uu____28269 = elim_delayed_subst_term t2  in
            let uu____28272 = FStar_List.map elim_branch branches  in
            (uu____28269, uu____28272)  in
          FStar_Syntax_Syntax.Tm_match uu____28246  in
        mk1 uu____28245
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____28403 =
          match uu____28403 with
          | (tc,topt) ->
              let uu____28438 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____28448 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____28448
                | FStar_Util.Inr c ->
                    let uu____28450 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____28450
                 in
              let uu____28451 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____28438, uu____28451)
           in
        let uu____28460 =
          let uu____28461 =
            let uu____28488 = elim_delayed_subst_term t2  in
            let uu____28491 = elim_ascription a  in
            (uu____28488, uu____28491, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____28461  in
        mk1 uu____28460
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3420_28554 = lb  in
          let uu____28555 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____28558 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3420_28554.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3420_28554.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____28555;
            FStar_Syntax_Syntax.lbeff =
              (uu___3420_28554.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____28558;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3420_28554.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3420_28554.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____28561 =
          let uu____28562 =
            let uu____28576 =
              let uu____28584 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____28584)  in
            let uu____28596 = elim_delayed_subst_term t2  in
            (uu____28576, uu____28596)  in
          FStar_Syntax_Syntax.Tm_let uu____28562  in
        mk1 uu____28561
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____28641 =
          let uu____28642 =
            let uu____28649 = elim_delayed_subst_term tm  in
            (uu____28649, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____28642  in
        mk1 uu____28641
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____28660 =
          let uu____28661 =
            let uu____28668 = elim_delayed_subst_term t2  in
            let uu____28671 = elim_delayed_subst_meta md  in
            (uu____28668, uu____28671)  in
          FStar_Syntax_Syntax.Tm_meta uu____28661  in
        mk1 uu____28660

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___17_28680  ->
         match uu___17_28680 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____28684 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____28684
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
        let uu____28707 =
          let uu____28708 =
            let uu____28717 = elim_delayed_subst_term t  in
            (uu____28717, uopt)  in
          FStar_Syntax_Syntax.Total uu____28708  in
        mk1 uu____28707
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____28734 =
          let uu____28735 =
            let uu____28744 = elim_delayed_subst_term t  in
            (uu____28744, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____28735  in
        mk1 uu____28734
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3453_28753 = ct  in
          let uu____28754 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____28757 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____28768 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3453_28753.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3453_28753.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28754;
            FStar_Syntax_Syntax.effect_args = uu____28757;
            FStar_Syntax_Syntax.flags = uu____28768
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___18_28771  ->
    match uu___18_28771 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____28806 =
          let uu____28827 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____28836 = FStar_List.map elim_delayed_subst_args args  in
          (uu____28827, uu____28836)  in
        FStar_Syntax_Syntax.Meta_pattern uu____28806
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____28891 =
          let uu____28898 = elim_delayed_subst_term t  in (m, uu____28898)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____28891
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____28910 =
          let uu____28919 = elim_delayed_subst_term t  in
          (m1, m2, uu____28919)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____28910
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
      (fun uu____28952  ->
         match uu____28952 with
         | (t,q) ->
             let uu____28971 = elim_delayed_subst_term t  in (uu____28971, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____28999  ->
         match uu____28999 with
         | (x,q) ->
             let uu____29018 =
               let uu___3479_29019 = x  in
               let uu____29020 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3479_29019.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3479_29019.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____29020
               }  in
             (uu____29018, q)) bs

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
            | (uu____29128,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____29160,FStar_Util.Inl t) ->
                let uu____29182 =
                  let uu____29189 =
                    let uu____29190 =
                      let uu____29205 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____29205)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____29190  in
                  FStar_Syntax_Syntax.mk uu____29189  in
                uu____29182 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____29218 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____29218 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____29250 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____29323 ->
                    let uu____29324 =
                      let uu____29333 =
                        let uu____29334 = FStar_Syntax_Subst.compress t4  in
                        uu____29334.FStar_Syntax_Syntax.n  in
                      (uu____29333, tc)  in
                    (match uu____29324 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____29363) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____29410) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____29455,FStar_Util.Inl uu____29456) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____29487 -> failwith "Impossible")
                 in
              (match uu____29250 with
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
          let uu____29626 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____29626 with
          | (univ_names1,binders1,tc) ->
              let uu____29700 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____29700)
  
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
          let uu____29754 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____29754 with
          | (univ_names1,binders1,tc) ->
              let uu____29828 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____29828)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____29870 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____29870 with
           | (univ_names1,binders1,typ1) ->
               let uu___3562_29910 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3562_29910.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3562_29910.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3562_29910.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3562_29910.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3562_29910.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3568_29925 = s  in
          let uu____29926 =
            let uu____29927 =
              let uu____29936 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29936, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29927  in
          {
            FStar_Syntax_Syntax.sigel = uu____29926;
            FStar_Syntax_Syntax.sigrng =
              (uu___3568_29925.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3568_29925.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3568_29925.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3568_29925.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3568_29925.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29955 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29955 with
           | (univ_names1,uu____29979,typ1) ->
               let uu___3582_30001 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3582_30001.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3582_30001.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3582_30001.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3582_30001.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3582_30001.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____30008 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____30008 with
           | (univ_names1,uu____30032,typ1) ->
               let uu___3593_30054 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3593_30054.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3593_30054.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3593_30054.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3593_30054.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3593_30054.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____30084 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____30084 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____30109 =
                            let uu____30110 =
                              let uu____30111 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____30111  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____30110
                             in
                          elim_delayed_subst_term uu____30109  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3609_30114 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3609_30114.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3609_30114.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3609_30114.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3609_30114.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3612_30115 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3612_30115.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3612_30115.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3612_30115.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3612_30115.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3612_30115.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3616_30122 = s  in
          let uu____30123 =
            let uu____30124 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____30124  in
          {
            FStar_Syntax_Syntax.sigel = uu____30123;
            FStar_Syntax_Syntax.sigrng =
              (uu___3616_30122.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3616_30122.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3616_30122.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3616_30122.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3616_30122.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____30128 = elim_uvars_aux_t env us [] t  in
          (match uu____30128 with
           | (us1,uu____30152,t1) ->
               let uu___3627_30174 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3627_30174.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3627_30174.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3627_30174.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3627_30174.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3627_30174.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____30176 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit
             in
          (match uu____30176 with
           | (univs1,binders,uu____30195) ->
               let uu____30216 =
                 let uu____30221 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____30221 with
                 | (univs_opening,univs2) ->
                     let uu____30244 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____30244)
                  in
               (match uu____30216 with
                | (univs_opening,univs_closing) ->
                    let uu____30247 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____30253 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____30254 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____30253, uu____30254)  in
                    (match uu____30247 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____30280 =
                           match uu____30280 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____30298 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____30298 with
                                | (us1,t1) ->
                                    let uu____30309 =
                                      let uu____30318 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____30323 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____30318, uu____30323)  in
                                    (match uu____30309 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____30346 =
                                           let uu____30355 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           let uu____30360 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  (n_us + n_binders))
                                              in
                                           (uu____30355, uu____30360)  in
                                         (match uu____30346 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____30384 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____30384
                                                 in
                                              let uu____30385 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____30385 with
                                               | (uu____30412,uu____30413,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____30436 =
                                                       let uu____30437 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____30437
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____30436
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____30446 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____30446 with
                           | (uu____30465,uu____30466,t1) -> t1  in
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
                             | uu____30542 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____30569 =
                               let uu____30570 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____30570.FStar_Syntax_Syntax.n  in
                             match uu____30569 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____30629 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____30663 =
                               let uu____30664 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____30664.FStar_Syntax_Syntax.n  in
                             match uu____30663 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____30687) ->
                                 let uu____30712 = destruct_action_body body
                                    in
                                 (match uu____30712 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____30761 ->
                                 let uu____30762 = destruct_action_body t  in
                                 (match uu____30762 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____30817 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____30817 with
                           | (action_univs,t) ->
                               let uu____30826 = destruct_action_typ_templ t
                                  in
                               (match uu____30826 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3711_30873 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3711_30873.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3711_30873.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3714_30875 = ed  in
                           let uu____30876 =
                             elim_tscheme ed.FStar_Syntax_Syntax.signature
                              in
                           let uu____30877 =
                             FStar_Syntax_Util.apply_eff_combinators
                               elim_tscheme
                               ed.FStar_Syntax_Syntax.combinators
                              in
                           let uu____30878 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___3714_30875.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3714_30875.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = uu____30876;
                             FStar_Syntax_Syntax.combinators = uu____30877;
                             FStar_Syntax_Syntax.actions = uu____30878;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3714_30875.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3717_30881 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3717_30881.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3717_30881.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3717_30881.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3717_30881.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___3717_30881.FStar_Syntax_Syntax.sigopts)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___19_30902 =
            match uu___19_30902 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30933 = elim_uvars_aux_t env us [] t  in
                (match uu____30933 with
                 | (us1,uu____30965,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3732_30996 = sub_eff  in
            let uu____30997 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____31000 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3732_30996.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3732_30996.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30997;
              FStar_Syntax_Syntax.lift = uu____31000
            }  in
          let uu___3735_31003 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3735_31003.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3735_31003.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3735_31003.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3735_31003.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts =
              (uu___3735_31003.FStar_Syntax_Syntax.sigopts)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____31013 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____31013 with
           | (univ_names1,binders1,comp1) ->
               let uu___3748_31053 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3748_31053.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3748_31053.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3748_31053.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3748_31053.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___3748_31053.FStar_Syntax_Syntax.sigopts)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____31056 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____31057 -> s
  
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
        let uu____31106 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____31106 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____31128 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____31128 with
             | (uu____31135,head_def) ->
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
      let uu____31141 = FStar_Syntax_Util.head_and_args t  in
      match uu____31141 with
      | (head1,args) ->
          let uu____31186 =
            let uu____31187 = FStar_Syntax_Subst.compress head1  in
            uu____31187.FStar_Syntax_Syntax.n  in
          (match uu____31186 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____31194;
                  FStar_Syntax_Syntax.vars = uu____31195;_},us)
               -> aux fv us args
           | uu____31201 -> FStar_Pervasives_Native.None)
  