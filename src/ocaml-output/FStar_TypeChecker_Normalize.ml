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
        (fun uu___115_1304  ->
           match () with
           | () ->
               let uu____1305 =
                 FStar_List.nth env x.FStar_Syntax_Syntax.index  in
               FStar_Pervasives_Native.snd uu____1305) ()
      with
      | uu___114_1322 ->
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
                 (fun uu___149_1506  ->
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
                                                 (let uu___243_1987 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___243_1987.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      = i;
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      (uu___243_1987.FStar_Syntax_Syntax.sort)
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
                         let uu___252_2001 = t  in
                         {
                           FStar_Syntax_Syntax.n =
                             (FStar_Syntax_Syntax.Tm_uvar
                                (uv, (s', (FStar_Pervasives_Native.snd s))));
                           FStar_Syntax_Syntax.pos =
                             (uu___252_2001.FStar_Syntax_Syntax.pos);
                           FStar_Syntax_Syntax.vars =
                             (uu___252_2001.FStar_Syntax_Syntax.vars)
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
                           let uu___268_2041 = x  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___268_2041.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___268_2041.FStar_Syntax_Syntax.index);
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
                             (let uu___360_2836 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___360_2836.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___360_2836.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = typ
                              })), uu____2820))
                       in
                    (match uu____2787 with
                     | (nm,body1) ->
                         let lb1 =
                           let uu___365_2854 = lb  in
                           {
                             FStar_Syntax_Syntax.lbname = nm;
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___365_2854.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp = typ;
                             FStar_Syntax_Syntax.lbeff =
                               (uu___365_2854.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = def;
                             FStar_Syntax_Syntax.lbattrs =
                               (uu___365_2854.FStar_Syntax_Syntax.lbattrs);
                             FStar_Syntax_Syntax.lbpos =
                               (uu___365_2854.FStar_Syntax_Syntax.lbpos)
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
                             (let uu___388_3004 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___388_3004.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___388_3004.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = ty
                              }))
                         in
                      let uu___391_3005 = lb  in
                      let uu____3006 =
                        non_tail_inline_closure_env cfg env2
                          lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname = nm;
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___391_3005.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = ty;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___391_3005.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____3006;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___391_3005.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___391_3005.FStar_Syntax_Syntax.lbpos)
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
                      let uu___449_3265 = FStar_Syntax_Util.abs bs1 t lopt1
                         in
                      {
                        FStar_Syntax_Syntax.n =
                          (uu___449_3265.FStar_Syntax_Syntax.n);
                        FStar_Syntax_Syntax.pos = r;
                        FStar_Syntax_Syntax.vars =
                          (uu___449_3265.FStar_Syntax_Syntax.vars)
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
                                ((let uu___486_3877 = p  in
                                  {
                                    FStar_Syntax_Syntax.v =
                                      (FStar_Syntax_Syntax.Pat_cons
                                         (fv, (FStar_List.rev pats1)));
                                    FStar_Syntax_Syntax.p =
                                      (uu___486_3877.FStar_Syntax_Syntax.p)
                                  }), env4))
                       | FStar_Syntax_Syntax.Pat_var x ->
                           let x1 =
                             let uu___490_3898 = x  in
                             let uu____3899 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___490_3898.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___490_3898.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3899
                             }  in
                           ((let uu___493_3913 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_var x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___493_3913.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_wild x ->
                           let x1 =
                             let uu___497_3924 = x  in
                             let uu____3925 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___497_3924.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___497_3924.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3925
                             }  in
                           ((let uu___500_3939 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_wild x1);
                               FStar_Syntax_Syntax.p =
                                 (uu___500_3939.FStar_Syntax_Syntax.p)
                             }), (dummy :: env3))
                       | FStar_Syntax_Syntax.Pat_dot_term (x,t1) ->
                           let x1 =
                             let uu___506_3955 = x  in
                             let uu____3956 =
                               non_tail_inline_closure_env cfg1 env3
                                 x.FStar_Syntax_Syntax.sort
                                in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___506_3955.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___506_3955.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = uu____3956
                             }  in
                           let t2 = non_tail_inline_closure_env cfg1 env3 t1
                              in
                           ((let uu___510_3973 = p  in
                             {
                               FStar_Syntax_Syntax.v =
                                 (FStar_Syntax_Syntax.Pat_dot_term (x1, t2));
                               FStar_Syntax_Syntax.p =
                                 (uu___510_3973.FStar_Syntax_Syntax.p)
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
                          let uu___565_4727 = b  in
                          let uu____4728 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___565_4727.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___565_4727.FStar_Syntax_Syntax.index);
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
                   let uu___598_4999 = c1  in
                   let uu____5000 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5000;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___598_4999.FStar_Syntax_Syntax.effect_name);
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
              let uu___615_5044 = rc  in
              let uu____5045 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___615_5044.FStar_Syntax_Syntax.residual_effect);
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
                                      let uu___650_5353 = bv  in
                                      let uu____5354 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___650_5353.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___650_5353.FStar_Syntax_Syntax.index);
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
          (let uu___738_5861 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___740_5864 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___740_5864.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___740_5864.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___740_5864.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___740_5864.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___740_5864.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___740_5864.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___740_5864.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___740_5864.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___740_5864.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___740_5864.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___740_5864.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___740_5864.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___740_5864.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___740_5864.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___740_5864.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___740_5864.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___740_5864.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___740_5864.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___740_5864.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___740_5864.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___740_5864.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___740_5864.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___740_5864.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___740_5864.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___740_5864.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___738_5861.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___738_5861.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___738_5861.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___738_5861.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___738_5861.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___738_5861.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___738_5861.FStar_TypeChecker_Cfg.reifying)
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
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___11_6670  ->
    match uu___11_6670 with
    | (App
        (uu____6674,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____6675;
                      FStar_Syntax_Syntax.vars = uu____6676;_},uu____6677,uu____6678))::uu____6679
        -> true
    | uu____6685 -> false
  
let firstn :
  'Auu____6696 .
    Prims.int ->
      'Auu____6696 Prims.list ->
        ('Auu____6696 Prims.list * 'Auu____6696 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___12_6753 =
        match uu___12_6753 with
        | (MemoLazy uu____6758)::s -> drop_irrel s
        | (UnivArgs uu____6768)::s -> drop_irrel s
        | s -> s  in
      let uu____6781 = drop_irrel stack  in
      match uu____6781 with
      | (App
          (uu____6785,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6786;
                        FStar_Syntax_Syntax.vars = uu____6787;_},uu____6788,uu____6789))::uu____6790
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6795 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6824) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6834) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6855  ->
                  match uu____6855 with
                  | (a,uu____6866) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6877 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6902 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6904 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6918 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6920 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6922 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6924 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6926 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6929 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6937 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6945 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6960 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6980 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____6996 -> true
    | FStar_Syntax_Syntax.Tm_match uu____7004 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7076  ->
                   match uu____7076 with
                   | (a,uu____7087) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7098) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____7197,args) ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7252  ->
                        match uu____7252 with
                        | (a,uu____7263) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7272,uu____7273,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7279,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7285 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7295 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7297 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7308 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7319 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7330 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7341 -> false
  
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
            let uu____7374 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7374 with
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
              (fun uu____7573  ->
                 fun uu____7574  ->
                   match (uu____7573, uu____7574) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7680 =
            match uu____7680 with
            | (x,y,z) ->
                let uu____7700 = FStar_Util.string_of_bool x  in
                let uu____7702 = FStar_Util.string_of_bool y  in
                let uu____7704 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7700 uu____7702
                  uu____7704
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7732  ->
                    let uu____7733 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7735 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7733 uu____7735);
               if b then reif else no)
            else
              if
                (let uu____7750 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7750)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7755  ->
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
                          ((is_rec,uu____7790),uu____7791);
                        FStar_Syntax_Syntax.sigrng = uu____7792;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7794;
                        FStar_Syntax_Syntax.sigattrs = uu____7795;_},uu____7796),uu____7797),uu____7798,uu____7799,uu____7800)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7907  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7909,uu____7910,uu____7911,uu____7912) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7979  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7982),uu____7983);
                        FStar_Syntax_Syntax.sigrng = uu____7984;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7986;
                        FStar_Syntax_Syntax.sigattrs = uu____7987;_},uu____7988),uu____7989),uu____7990,uu____7991,uu____7992)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8099  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8101,FStar_Pervasives_Native.Some
                    uu____8102,uu____8103,uu____8104) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8172  ->
                           let uu____8173 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8173);
                      (let uu____8176 =
                         let uu____8188 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8214 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8214
                            in
                         let uu____8226 =
                           let uu____8238 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8264 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8264
                              in
                           let uu____8280 =
                             let uu____8292 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8318 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8318
                                in
                             [uu____8292]  in
                           uu____8238 :: uu____8280  in
                         uu____8188 :: uu____8226  in
                       comb_or uu____8176))
                 | (uu____8366,uu____8367,FStar_Pervasives_Native.Some
                    uu____8368,uu____8369) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8437  ->
                           let uu____8438 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8438);
                      (let uu____8441 =
                         let uu____8453 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8479 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8479
                            in
                         let uu____8491 =
                           let uu____8503 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8529 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8529
                              in
                           let uu____8545 =
                             let uu____8557 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8583 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8583
                                in
                             [uu____8557]  in
                           uu____8503 :: uu____8545  in
                         uu____8453 :: uu____8491  in
                       comb_or uu____8441))
                 | (uu____8631,uu____8632,uu____8633,FStar_Pervasives_Native.Some
                    uu____8634) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8702  ->
                           let uu____8703 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8703);
                      (let uu____8706 =
                         let uu____8718 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8744 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8744
                            in
                         let uu____8756 =
                           let uu____8768 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8794 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8794
                              in
                           let uu____8810 =
                             let uu____8822 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8848 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8848
                                in
                             [uu____8822]  in
                           uu____8768 :: uu____8810  in
                         uu____8718 :: uu____8756  in
                       comb_or uu____8706))
                 | uu____8896 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8942  ->
                           let uu____8943 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____8945 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____8947 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____8943 uu____8945 uu____8947);
                      (let uu____8950 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___13_8956  ->
                                 match uu___13_8956 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____8962 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____8962 l))
                          in
                       FStar_All.pipe_left yesno uu____8950)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____8978  ->
               let uu____8979 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____8981 =
                 let uu____8983 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____8983  in
               let uu____8984 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____8979 uu____8981 uu____8984);
          (match res with
           | (false ,uu____8987,uu____8988) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____9013 ->
               let uu____9023 =
                 let uu____9025 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9025
                  in
               FStar_All.pipe_left failwith uu____9023)
  
let decide_unfolding :
  'Auu____9044 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____9044 ->
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
                    let uu___1159_9113 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1161_9116 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1161_9116.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1161_9116.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1159_9113.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1159_9113.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1159_9113.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1159_9113.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1159_9113.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1159_9113.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1159_9113.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1159_9113.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____9178 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____9178
                    | h::t -> e :: h :: t  in
                  let refl =
                    let uu____9190 =
                      let uu____9197 =
                        let uu____9198 =
                          let uu____9199 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____9199  in
                        FStar_Syntax_Syntax.Tm_constant uu____9198  in
                      FStar_Syntax_Syntax.mk uu____9197  in
                    uu____9190 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let refl1 =
                    let uu____9203 =
                      let uu____9214 =
                        FStar_Syntax_Syntax.iarg FStar_Syntax_Syntax.tun  in
                      [uu____9214]  in
                    FStar_Syntax_Util.mk_app refl uu____9203  in
                  let stack1 =
                    push1
                      (App
                         (env, refl1, FStar_Pervasives_Native.None,
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
    let uu____9304 =
      let uu____9305 = FStar_Syntax_Subst.compress t  in
      uu____9305.FStar_Syntax_Syntax.n  in
    match uu____9304 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9336 =
          let uu____9337 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9337.FStar_Syntax_Syntax.n  in
        (match uu____9336 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.of_int (3)))
             ->
             let f =
               let uu____9354 =
                 let uu____9361 =
                   let uu____9372 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9372 FStar_List.tl  in
                 FStar_All.pipe_right uu____9361 FStar_List.hd  in
               FStar_All.pipe_right uu____9354 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9471 -> FStar_Pervasives_Native.None)
    | uu____9472 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9751 ->
                   let uu____9774 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9774
               | uu____9777 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9787  ->
               let uu____9788 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9790 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9792 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9794 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9802 =
                 let uu____9804 =
                   let uu____9807 = firstn (Prims.of_int (4)) stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9807
                    in
                 stack_to_string uu____9804  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9788 uu____9790 uu____9792 uu____9794 uu____9802);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9835  ->
               let uu____9836 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9836);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9842  ->
                     let uu____9843 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9843);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9846 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9850  ->
                     let uu____9851 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9851);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____9854 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9858  ->
                     let uu____9859 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9859);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9862 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9866  ->
                     let uu____9867 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9867);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9870;
                 FStar_Syntax_Syntax.fv_delta = uu____9871;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9875  ->
                     let uu____9876 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9876);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9879;
                 FStar_Syntax_Syntax.fv_delta = uu____9880;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9881);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9891  ->
                     let uu____9892 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9892);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____9898 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____9898 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _9901) when
                    _9901 = Prims.int_zero ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9905  ->
                          let uu____9906 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9906);
                     rebuild cfg env stack t1)
                | uu____9909 ->
                    let uu____9912 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____9912 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____9939 ->
               let uu____9946 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____9946
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9974 = is_norm_request hd1 args  in
                  uu____9974 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____9980 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____9980))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____10008 = is_norm_request hd1 args  in
                  uu____10008 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1269_10015 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1271_10018 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1271_10018.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1269_10015.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1269_10015.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1269_10015.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1269_10015.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1269_10015.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1269_10015.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____10025 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____10025 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____10061  ->
                                 fun stack1  ->
                                   match uu____10061 with
                                   | (a,aq) ->
                                       let uu____10073 =
                                         let uu____10074 =
                                           let uu____10081 =
                                             let uu____10082 =
                                               let uu____10114 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____10114, false)
                                                in
                                             Clos uu____10082  in
                                           (uu____10081, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10074  in
                                       uu____10073 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10182  ->
                            let uu____10183 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10183);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10210 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____10210)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____10221 =
                            let uu____10223 =
                              let uu____10225 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____10225  in
                            FStar_Util.string_of_int uu____10223  in
                          let uu____10232 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____10234 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____10221 uu____10232 uu____10234)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10253 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____10253)
                      else ();
                      (let delta_level =
                         let uu____10261 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___14_10268  ->
                                   match uu___14_10268 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____10270 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____10272 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____10276 -> true
                                   | uu____10280 -> false))
                            in
                         if uu____10261
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1312_10288 = cfg  in
                         let uu____10289 =
                           let uu___1314_10290 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1314_10290.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____10289;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1312_10288.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1312_10288.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1312_10288.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1312_10288.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1312_10288.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1312_10288.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____10298 =
                             let uu____10299 =
                               let uu____10304 = FStar_Util.now ()  in
                               (t1, uu____10304)  in
                             Debug uu____10299  in
                           uu____10298 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10309 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10309
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10320 =
                      let uu____10327 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10327, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10320  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10336 = lookup_bvar env x  in
               (match uu____10336 with
                | Univ uu____10337 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____10391 = FStar_ST.op_Bang r  in
                      (match uu____10391 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10487  ->
                                 let uu____10488 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10490 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10488
                                   uu____10490);
                            (let uu____10493 = maybe_weakly_reduced t'  in
                             if uu____10493
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____10496 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10540)::uu____10541 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10552,uu____10553))::stack_rest ->
                    (match c with
                     | Univ uu____10557 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10566 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10596  ->
                                    let uu____10597 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10597);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10633  ->
                                    let uu____10634 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10634);
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
                       (fun uu____10682  ->
                          let uu____10683 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10683);
                     norm cfg env stack1 t1)
                | (Match uu____10686)::uu____10687 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10702 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10702 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10738  -> dummy :: env1) env)
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
                                          let uu____10782 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10782)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1432_10790 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_10790.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_10790.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10791 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10797  ->
                                 let uu____10798 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10798);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1439_10813 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1439_10813.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1439_10813.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1439_10813.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1439_10813.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1439_10813.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1439_10813.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1439_10813.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1439_10813.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____10817)::uu____10818 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10829 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10829 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10865  -> dummy :: env1) env)
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
                                          let uu____10909 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10909)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1432_10917 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_10917.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_10917.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10918 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10924  ->
                                 let uu____10925 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10925);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1439_10940 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1439_10940.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1439_10940.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1439_10940.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1439_10940.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1439_10940.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1439_10940.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1439_10940.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1439_10940.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10944)::uu____10945 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10958 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10958 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10994  -> dummy :: env1) env)
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
                                          let uu____11038 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11038)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1432_11046 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_11046.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_11046.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11047 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11053  ->
                                 let uu____11054 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11054);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1439_11069 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1439_11069.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1439_11069.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1439_11069.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1439_11069.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1439_11069.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1439_11069.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1439_11069.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1439_11069.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11073)::uu____11074 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11089 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11089 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11125  -> dummy :: env1) env)
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
                                          let uu____11169 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11169)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1432_11177 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_11177.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_11177.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11178 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11184  ->
                                 let uu____11185 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11185);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1439_11200 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1439_11200.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1439_11200.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1439_11200.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1439_11200.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1439_11200.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1439_11200.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1439_11200.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1439_11200.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11204)::uu____11205 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11220 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11220 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11256  -> dummy :: env1) env)
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
                                          let uu____11300 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11300)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1432_11308 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_11308.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_11308.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11309 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11315  ->
                                 let uu____11316 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11316);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1439_11331 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1439_11331.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1439_11331.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1439_11331.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1439_11331.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1439_11331.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1439_11331.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1439_11331.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1439_11331.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11335)::uu____11336 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11355 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11355 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11391  -> dummy :: env1) env)
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
                                          let uu____11435 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11435)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1432_11443 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_11443.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_11443.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11444 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11450  ->
                                 let uu____11451 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11451);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1439_11466 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1439_11466.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1439_11466.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1439_11466.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1439_11466.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1439_11466.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1439_11466.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1439_11466.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1439_11466.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____11474 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11474 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11510  -> dummy :: env1) env)
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
                                          let uu____11554 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11554)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1432_11562 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1432_11562.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1432_11562.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11563 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11569  ->
                                 let uu____11570 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11570);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1439_11585 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1439_11585.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1439_11585.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1439_11585.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1439_11585.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1439_11585.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1439_11585.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1439_11585.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1439_11585.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let strict_args =
                 let uu____11621 =
                   let uu____11622 = FStar_Syntax_Util.un_uinst head1  in
                   uu____11622.FStar_Syntax_Syntax.n  in
                 match uu____11621 with
                 | FStar_Syntax_Syntax.Tm_fvar fv ->
                     FStar_TypeChecker_Env.fv_has_strict_args
                       cfg.FStar_TypeChecker_Cfg.tcenv fv
                 | uu____11631 -> FStar_Pervasives_Native.None  in
               (match strict_args with
                | FStar_Pervasives_Native.None  ->
                    let stack1 =
                      FStar_All.pipe_right stack
                        (FStar_List.fold_right
                           (fun uu____11652  ->
                              fun stack1  ->
                                match uu____11652 with
                                | (a,aq) ->
                                    let uu____11664 =
                                      let uu____11665 =
                                        let uu____11672 =
                                          let uu____11673 =
                                            let uu____11705 =
                                              FStar_Util.mk_ref
                                                FStar_Pervasives_Native.None
                                               in
                                            (env, a, uu____11705, false)  in
                                          Clos uu____11673  in
                                        (uu____11672, aq,
                                          (t1.FStar_Syntax_Syntax.pos))
                                         in
                                      Arg uu____11665  in
                                    uu____11664 :: stack1) args)
                       in
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____11773  ->
                          let uu____11774 =
                            FStar_All.pipe_left FStar_Util.string_of_int
                              (FStar_List.length args)
                             in
                          FStar_Util.print1 "\tPushed %s arguments\n"
                            uu____11774);
                     norm cfg env stack1 head1)
                | FStar_Pervasives_Native.Some strict_args1 ->
                    let norm_args =
                      FStar_All.pipe_right args
                        (FStar_List.map
                           (fun uu____11825  ->
                              match uu____11825 with
                              | (a,i) ->
                                  let uu____11836 = norm cfg env [] a  in
                                  (uu____11836, i)))
                       in
                    let norm_args_len = FStar_List.length norm_args  in
                    let uu____11842 =
                      FStar_All.pipe_right strict_args1
                        (FStar_List.for_all
                           (fun i  ->
                              if i >= norm_args_len
                              then false
                              else
                                (let uu____11857 = FStar_List.nth norm_args i
                                    in
                                 match uu____11857 with
                                 | (arg_i,uu____11868) ->
                                     let uu____11869 =
                                       FStar_Syntax_Util.head_and_args arg_i
                                        in
                                     (match uu____11869 with
                                      | (head2,uu____11888) ->
                                          let uu____11913 =
                                            let uu____11914 =
                                              FStar_Syntax_Util.un_uinst
                                                head2
                                               in
                                            uu____11914.FStar_Syntax_Syntax.n
                                             in
                                          (match uu____11913 with
                                           | FStar_Syntax_Syntax.Tm_constant
                                               uu____11918 -> true
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               let uu____11921 =
                                                 FStar_Syntax_Syntax.lid_of_fv
                                                   fv
                                                  in
                                               FStar_TypeChecker_Env.is_datacon
                                                 cfg.FStar_TypeChecker_Cfg.tcenv
                                                 uu____11921
                                           | uu____11922 -> false)))))
                       in
                    if uu____11842
                    then
                      let stack1 =
                        FStar_All.pipe_right stack
                          (FStar_List.fold_right
                             (fun uu____11939  ->
                                fun stack1  ->
                                  match uu____11939 with
                                  | (a,aq) ->
                                      let uu____11951 =
                                        let uu____11952 =
                                          let uu____11959 =
                                            let uu____11960 =
                                              let uu____11992 =
                                                FStar_Util.mk_ref
                                                  (FStar_Pervasives_Native.Some
                                                     ([], a))
                                                 in
                                              (env, a, uu____11992, false)
                                               in
                                            Clos uu____11960  in
                                          (uu____11959, aq,
                                            (t1.FStar_Syntax_Syntax.pos))
                                           in
                                        Arg uu____11952  in
                                      uu____11951 :: stack1) norm_args)
                         in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____12074  ->
                            let uu____12075 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____12075);
                       norm cfg env stack1 head1)
                    else
                      (let head2 = closure_as_term cfg env head1  in
                       let term =
                         FStar_Syntax_Syntax.mk_Tm_app head2 norm_args
                           FStar_Pervasives_Native.None
                           t1.FStar_Syntax_Syntax.pos
                          in
                       rebuild cfg env stack term))
           | FStar_Syntax_Syntax.Tm_refine (x,uu____12095) when
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
                             ((let uu___1501_12140 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1501_12140.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1501_12140.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____12141 ->
                      let uu____12156 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____12156)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____12160 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____12160 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____12191 =
                          let uu____12192 =
                            let uu____12199 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1510_12205 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1510_12205.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1510_12205.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____12199)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____12192  in
                        mk uu____12191 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____12229 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____12229
               else
                 (let uu____12232 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____12232 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____12240 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____12266  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____12240 c1  in
                      let t2 =
                        let uu____12290 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____12290 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12403)::uu____12404 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12417  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12419)::uu____12420 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12431  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12433,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12434;
                                   FStar_Syntax_Syntax.vars = uu____12435;_},uu____12436,uu____12437))::uu____12438
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12445  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12447)::uu____12448 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12459  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12461 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12464  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12469  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12495 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12495
                         | FStar_Util.Inr c ->
                             let uu____12509 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12509
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12532 =
                               let uu____12533 =
                                 let uu____12560 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12560, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12533
                                in
                             mk uu____12532 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12595 ->
                           let uu____12596 =
                             let uu____12597 =
                               let uu____12598 =
                                 let uu____12625 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12625, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12598
                                in
                             mk uu____12597 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12596))))
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
                   let uu___1589_12703 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1591_12706 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1591_12706.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1589_12703.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1589_12703.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1589_12703.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1589_12703.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1589_12703.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1589_12703.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1589_12703.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1589_12703.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____12747 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12747 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1604_12767 = cfg  in
                               let uu____12768 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1604_12767.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12768;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1604_12767.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1604_12767.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1604_12767.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1604_12767.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1604_12767.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1604_12767.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1604_12767.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____12775 =
                                 let uu____12776 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12776  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12775
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1611_12779 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1611_12779.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1611_12779.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1611_12779.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1611_12779.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12780 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12780
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12793,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12794;
                               FStar_Syntax_Syntax.lbunivs = uu____12795;
                               FStar_Syntax_Syntax.lbtyp = uu____12796;
                               FStar_Syntax_Syntax.lbeff = uu____12797;
                               FStar_Syntax_Syntax.lbdef = uu____12798;
                               FStar_Syntax_Syntax.lbattrs = uu____12799;
                               FStar_Syntax_Syntax.lbpos = uu____12800;_}::uu____12801),uu____12802)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12848 =
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
               if uu____12848
               then
                 let binder =
                   let uu____12852 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12852  in
                 let env1 =
                   let uu____12862 =
                     let uu____12869 =
                       let uu____12870 =
                         let uu____12902 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12902,
                           false)
                          in
                       Clos uu____12870  in
                     ((FStar_Pervasives_Native.Some binder), uu____12869)  in
                   uu____12862 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____12977  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____12984  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12986 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12986))
                 else
                   (let uu____12989 =
                      let uu____12994 =
                        let uu____12995 =
                          let uu____13002 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____13002
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12995]  in
                      FStar_Syntax_Subst.open_term uu____12994 body  in
                    match uu____12989 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____13029  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____13038 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____13038  in
                            FStar_Util.Inl
                              (let uu___1653_13054 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1653_13054.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1653_13054.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____13057  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___1658_13060 = lb  in
                             let uu____13061 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1658_13060.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1658_13060.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____13061;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1658_13060.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1658_13060.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____13090  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___1665_13115 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___1665_13115.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___1665_13115.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___1665_13115.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___1665_13115.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___1665_13115.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___1665_13115.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___1665_13115.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___1665_13115.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____13119  ->
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
               let uu____13140 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____13140 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____13176 =
                               let uu___1681_13177 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1681_13177.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1681_13177.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____13176  in
                           let uu____13178 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____13178 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____13204 =
                                   FStar_List.map (fun uu____13220  -> dummy)
                                     lbs1
                                    in
                                 let uu____13221 =
                                   let uu____13230 =
                                     FStar_List.map
                                       (fun uu____13252  -> dummy) xs1
                                      in
                                   FStar_List.append uu____13230 env  in
                                 FStar_List.append uu____13204 uu____13221
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____13278 =
                                       let uu___1695_13279 = rc  in
                                       let uu____13280 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1695_13279.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____13280;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1695_13279.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____13278
                                 | uu____13289 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1700_13295 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1700_13295.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1700_13295.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1700_13295.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1700_13295.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____13305 =
                        FStar_List.map (fun uu____13321  -> dummy) lbs2  in
                      FStar_List.append uu____13305 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____13329 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____13329 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1709_13345 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1709_13345.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1709_13345.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____13379 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13379
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13400 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13478  ->
                        match uu____13478 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1725_13603 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1725_13603.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1725_13603.FStar_Syntax_Syntax.sort)
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
               (match uu____13400 with
                | (rec_env,memos,uu____13794) ->
                    let uu____13849 =
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
                             let uu____14098 =
                               let uu____14105 =
                                 let uu____14106 =
                                   let uu____14138 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____14138, false)
                                    in
                                 Clos uu____14106  in
                               (FStar_Pervasives_Native.None, uu____14105)
                                in
                             uu____14098 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____14223  ->
                     let uu____14224 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____14224);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____14248 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____14252::uu____14253 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____14258) ->
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
                             | uu____14337 -> norm cfg env stack head1)
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
                                  let uu____14385 =
                                    let uu____14406 =
                                      norm_pattern_args cfg env args  in
                                    (names2, uu____14406)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14385
                              | uu____14435 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14441 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14465 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14479 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14493 =
                        let uu____14495 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14497 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14495 uu____14497
                         in
                      failwith uu____14493
                    else
                      (let uu____14502 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____14502)
                | uu____14503 -> norm cfg env stack t2))

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
              let uu____14512 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14512 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14526  ->
                        let uu____14527 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14527);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14540  ->
                        let uu____14541 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14543 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14541 uu____14543);
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
                      | (UnivArgs (us',uu____14556))::stack1 ->
                          ((let uu____14565 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14565
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14573 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14573) us'
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
                      | uu____14609 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14612 ->
                          let uu____14615 =
                            let uu____14617 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14617
                             in
                          failwith uu____14615
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
                  let uu___1837_14645 = cfg  in
                  let uu____14646 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____14646;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1837_14645.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1837_14645.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1837_14645.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1837_14645.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1837_14645.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1837_14645.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1837_14645.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____14677,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14678;
                                    FStar_Syntax_Syntax.vars = uu____14679;_},uu____14680,uu____14681))::uu____14682
                     -> ()
                 | uu____14687 ->
                     let uu____14690 =
                       let uu____14692 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14692
                        in
                     failwith uu____14690);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____14701  ->
                      let uu____14702 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____14704 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____14702
                        uu____14704);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____14708 =
                    let uu____14709 = FStar_Syntax_Subst.compress head3  in
                    uu____14709.FStar_Syntax_Syntax.n  in
                  match uu____14708 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____14730 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____14730
                         in
                      let uu____14731 =
                        (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                         in
                      (match uu____14731 with
                       | (uu____14732,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14742 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____14753 =
                                    let uu____14754 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14754.FStar_Syntax_Syntax.n  in
                                  match uu____14753 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____14760,uu____14761))
                                      ->
                                      let uu____14770 =
                                        let uu____14771 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____14771.FStar_Syntax_Syntax.n  in
                                      (match uu____14770 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____14777,msrc,uu____14779))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____14788 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____14788
                                       | uu____14789 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____14790 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____14791 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____14791 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___1909_14796 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___1909_14796.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___1909_14796.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___1909_14796.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___1909_14796.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___1909_14796.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____14797 = FStar_List.tl stack
                                        in
                                     let uu____14798 =
                                       let uu____14799 =
                                         let uu____14806 =
                                           let uu____14807 =
                                             let uu____14821 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____14821)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____14807
                                            in
                                         FStar_Syntax_Syntax.mk uu____14806
                                          in
                                       uu____14799
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____14797 uu____14798
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____14837 =
                                       let uu____14839 = is_return body  in
                                       match uu____14839 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____14844;
                                             FStar_Syntax_Syntax.vars =
                                               uu____14845;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____14848 -> false  in
                                     if uu____14837
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
                                          let uu____14872 =
                                            let uu____14879 =
                                              let uu____14880 =
                                                let uu____14899 =
                                                  let uu____14908 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____14908]  in
                                                (uu____14899, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____14880
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____14879
                                             in
                                          uu____14872
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____14947 =
                                            let uu____14948 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____14948.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14947 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____14954::uu____14955::[])
                                              ->
                                              let uu____14960 =
                                                let uu____14967 =
                                                  let uu____14968 =
                                                    let uu____14975 =
                                                      let uu____14976 =
                                                        let uu____14977 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____14977
                                                         in
                                                      let uu____14978 =
                                                        let uu____14981 =
                                                          let uu____14982 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____14982
                                                           in
                                                        [uu____14981]  in
                                                      uu____14976 ::
                                                        uu____14978
                                                       in
                                                    (bind1, uu____14975)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____14968
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____14967
                                                 in
                                              uu____14960
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____14985 -> bind_repr  in
                                        let maybe_range_arg =
                                          let uu____14997 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____14997
                                          then
                                            let uu____15010 =
                                              let uu____15019 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____15019
                                               in
                                            let uu____15020 =
                                              let uu____15031 =
                                                let uu____15040 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____15040
                                                 in
                                              [uu____15031]  in
                                            uu____15010 :: uu____15020
                                          else []  in
                                        let maybe_wphead =
                                          if ed.FStar_Syntax_Syntax.spec_dm4f
                                          then
                                            let uu____15097 =
                                              FStar_Syntax_Syntax.as_arg
                                                FStar_Syntax_Syntax.tun
                                               in
                                            [uu____15097]
                                          else []  in
                                        let maybe_wpbody =
                                          if ed.FStar_Syntax_Syntax.spec_dm4f
                                          then
                                            let uu____15154 =
                                              FStar_Syntax_Syntax.as_arg
                                                FStar_Syntax_Syntax.tun
                                               in
                                            [uu____15154]
                                          else []  in
                                        let reified =
                                          let uu____15192 =
                                            let uu____15199 =
                                              let uu____15200 =
                                                let uu____15217 =
                                                  let uu____15228 =
                                                    let uu____15239 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____15248 =
                                                      let uu____15259 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____15259]  in
                                                    uu____15239 ::
                                                      uu____15248
                                                     in
                                                  let uu____15292 =
                                                    let uu____15303 =
                                                      let uu____15314 =
                                                        let uu____15325 =
                                                          let uu____15336 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              head4
                                                             in
                                                          [uu____15336]  in
                                                        let uu____15361 =
                                                          let uu____15372 =
                                                            let uu____15383 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____15383]  in
                                                          FStar_List.append
                                                            maybe_wpbody
                                                            uu____15372
                                                           in
                                                        FStar_List.append
                                                          uu____15325
                                                          uu____15361
                                                         in
                                                      FStar_List.append
                                                        maybe_wphead
                                                        uu____15314
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____15303
                                                     in
                                                  FStar_List.append
                                                    uu____15228 uu____15292
                                                   in
                                                (bind_inst, uu____15217)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____15200
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____15199
                                             in
                                          uu____15192
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____15464  ->
                                             let uu____15465 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____15467 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____15465 uu____15467);
                                        (let uu____15470 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____15470 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____15498 = FStar_Options.defensive ()  in
                        if uu____15498
                        then
                          let is_arg_impure uu____15513 =
                            match uu____15513 with
                            | (e,q) ->
                                let uu____15527 =
                                  let uu____15528 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____15528.FStar_Syntax_Syntax.n  in
                                (match uu____15527 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____15544 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____15544
                                 | uu____15546 -> false)
                             in
                          let uu____15548 =
                            let uu____15550 =
                              let uu____15561 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____15561 :: args  in
                            FStar_Util.for_some is_arg_impure uu____15550  in
                          (if uu____15548
                           then
                             let uu____15587 =
                               let uu____15593 =
                                 let uu____15595 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____15595
                                  in
                               (FStar_Errors.Warning_Defensive, uu____15593)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____15587
                           else ())
                        else ());
                       (let fallback1 uu____15608 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15612  ->
                               let uu____15613 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____15613 "");
                          (let uu____15617 = FStar_List.tl stack  in
                           let uu____15618 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____15617 uu____15618)
                           in
                        let fallback2 uu____15624 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15628  ->
                               let uu____15629 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____15629 "");
                          (let uu____15633 = FStar_List.tl stack  in
                           let uu____15634 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____15633 uu____15634)
                           in
                        let uu____15639 =
                          let uu____15640 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____15640.FStar_Syntax_Syntax.n  in
                        match uu____15639 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____15646 =
                              let uu____15648 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____15648  in
                            if uu____15646
                            then fallback1 ()
                            else
                              (let uu____15653 =
                                 let uu____15655 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____15655  in
                               if uu____15653
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____15672 =
                                      let uu____15677 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____15677 args
                                       in
                                    uu____15672 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____15678 = FStar_List.tl stack  in
                                  norm cfg env uu____15678 t1))
                        | uu____15679 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____15681) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____15705 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____15705  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____15709  ->
                            let uu____15710 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____15710);
                       (let uu____15713 = FStar_List.tl stack  in
                        norm cfg env uu____15713 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____15834  ->
                                match uu____15834 with
                                | (pat,wopt,tm) ->
                                    let uu____15882 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____15882)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____15914 = FStar_List.tl stack  in
                      norm cfg env uu____15914 tm
                  | uu____15915 -> fallback ()))

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
              (fun uu____15929  ->
                 let uu____15930 = FStar_Ident.string_of_lid msrc  in
                 let uu____15932 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15934 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15930
                   uu____15932 uu____15934);
            (let uu____15937 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____15937
             then
               let ed =
                 let uu____15941 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15941  in
               let uu____15942 =
                 (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                  in
               match uu____15942 with
               | (uu____15943,return_repr) ->
                   let return_inst =
                     let uu____15956 =
                       let uu____15957 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15957.FStar_Syntax_Syntax.n  in
                     match uu____15956 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15963::[]) ->
                         let uu____15968 =
                           let uu____15975 =
                             let uu____15976 =
                               let uu____15983 =
                                 let uu____15984 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15984]  in
                               (return_tm, uu____15983)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15976  in
                           FStar_Syntax_Syntax.mk uu____15975  in
                         uu____15968 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15987 -> return_repr  in
                   let uu____15988 =
                     let uu____15995 =
                       let uu____15996 =
                         let uu____16013 =
                           let uu____16024 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____16033 =
                             let uu____16044 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____16044]  in
                           uu____16024 :: uu____16033  in
                         (return_inst, uu____16013)  in
                       FStar_Syntax_Syntax.Tm_app uu____15996  in
                     FStar_Syntax_Syntax.mk uu____15995  in
                   uu____15988 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____16091 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____16091 with
                | FStar_Pervasives_Native.None  ->
                    let uu____16094 =
                      let uu____16096 = FStar_Ident.text_of_lid msrc  in
                      let uu____16098 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____16096 uu____16098
                       in
                    failwith uu____16094
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16101;
                      FStar_TypeChecker_Env.mtarget = uu____16102;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16103;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____16125 =
                      let uu____16127 = FStar_Ident.text_of_lid msrc  in
                      let uu____16129 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____16127 uu____16129
                       in
                    failwith uu____16125
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____16132;
                      FStar_TypeChecker_Env.mtarget = uu____16133;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____16134;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____16169 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____16170 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____16169 t FStar_Syntax_Syntax.tun uu____16170))

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
                (fun uu____16240  ->
                   match uu____16240 with
                   | (a,imp) ->
                       let uu____16259 = norm cfg env [] a  in
                       (uu____16259, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____16269  ->
             let uu____16270 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____16272 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____16270 uu____16272);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16298 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16301  -> FStar_Pervasives_Native.Some _16301)
                     uu____16298
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2063_16302 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2063_16302.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2063_16302.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____16324 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _16327  -> FStar_Pervasives_Native.Some _16327)
                     uu____16324
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2074_16328 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2074_16328.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2074_16328.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____16373  ->
                      match uu____16373 with
                      | (a,i) ->
                          let uu____16393 = norm cfg env [] a  in
                          (uu____16393, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___15_16415  ->
                       match uu___15_16415 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____16419 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____16419
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2091_16427 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2093_16430 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2093_16430.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2091_16427.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2091_16427.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____16434 = b  in
        match uu____16434 with
        | (x,imp) ->
            let x1 =
              let uu___2101_16442 = x  in
              let uu____16443 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2101_16442.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2101_16442.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____16443
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____16454 =
                    let uu____16455 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____16455  in
                  FStar_Pervasives_Native.Some uu____16454
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16466 =
          FStar_List.fold_left
            (fun uu____16500  ->
               fun b  ->
                 match uu____16500 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16466 with | (nbs,uu____16580) -> FStar_List.rev nbs

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
            let uu____16612 =
              let uu___2126_16613 = rc  in
              let uu____16614 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2126_16613.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16614;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2126_16613.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____16612
        | uu____16623 -> lopt

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
            (let uu____16633 = FStar_Syntax_Print.term_to_string tm  in
             let uu____16635 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____16633 uu____16635)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___16_16647  ->
      match uu___16_16647 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____16660 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____16660 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____16664 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____16664)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____16672 = norm_cb cfg  in
            reduce_primops uu____16672 cfg env tm  in
          let uu____16677 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____16677
          then tm1
          else
            (let w t =
               let uu___2154_16696 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2154_16696.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2154_16696.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____16708 =
                 let uu____16709 = FStar_Syntax_Util.unmeta t  in
                 uu____16709.FStar_Syntax_Syntax.n  in
               match uu____16708 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____16721 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____16785)::args1,(bv,uu____16788)::bs1) ->
                   let uu____16842 =
                     let uu____16843 = FStar_Syntax_Subst.compress t  in
                     uu____16843.FStar_Syntax_Syntax.n  in
                   (match uu____16842 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16848 -> false)
               | ([],[]) -> true
               | (uu____16879,uu____16880) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____16931 = FStar_Syntax_Print.term_to_string t  in
                  let uu____16933 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____16931
                    uu____16933)
               else ();
               (let uu____16938 = FStar_Syntax_Util.head_and_args' t  in
                match uu____16938 with
                | (hd1,args) ->
                    let uu____16977 =
                      let uu____16978 = FStar_Syntax_Subst.compress hd1  in
                      uu____16978.FStar_Syntax_Syntax.n  in
                    (match uu____16977 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____16986 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____16988 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____16990 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____16986 uu____16988 uu____16990)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____16995 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____17013 = FStar_Syntax_Print.term_to_string t  in
                  let uu____17015 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____17013
                    uu____17015)
               else ();
               (let uu____17020 = FStar_Syntax_Util.is_squash t  in
                match uu____17020 with
                | FStar_Pervasives_Native.Some (uu____17031,t') ->
                    is_applied bs t'
                | uu____17043 ->
                    let uu____17052 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____17052 with
                     | FStar_Pervasives_Native.Some (uu____17063,t') ->
                         is_applied bs t'
                     | uu____17075 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____17099 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17099 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____17106)::(q,uu____17108)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17151 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____17153 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____17151 uu____17153)
                    else ();
                    (let uu____17158 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____17158 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____17163 =
                           let uu____17164 = FStar_Syntax_Subst.compress p
                              in
                           uu____17164.FStar_Syntax_Syntax.n  in
                         (match uu____17163 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____17175 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17175))
                          | uu____17178 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____17181)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____17206 =
                           let uu____17207 = FStar_Syntax_Subst.compress p1
                              in
                           uu____17207.FStar_Syntax_Syntax.n  in
                         (match uu____17206 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____17218 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____17218))
                          | uu____17221 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,pats,phi1)) ->
                         let uu____17225 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____17225 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____17230 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____17230 with
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
                                     let uu____17244 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17244))
                               | uu____17247 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____17252)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____17277 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____17277 with
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
                                     let uu____17291 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____17291))
                               | uu____17294 -> FStar_Pervasives_Native.None)
                          | uu____17297 -> FStar_Pervasives_Native.None)
                     | uu____17300 -> FStar_Pervasives_Native.None))
               | uu____17303 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____17316 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____17316 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____17322)::[],uu____17323,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____17343 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____17345 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____17343
                         uu____17345)
                    else ();
                    is_quantified_const bv phi')
               | uu____17350 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____17365 =
                 let uu____17366 = FStar_Syntax_Subst.compress phi  in
                 uu____17366.FStar_Syntax_Syntax.n  in
               match uu____17365 with
               | FStar_Syntax_Syntax.Tm_match (uu____17372,br::brs) ->
                   let uu____17439 = br  in
                   (match uu____17439 with
                    | (uu____17457,uu____17458,e) ->
                        let r =
                          let uu____17480 = simp_t e  in
                          match uu____17480 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____17492 =
                                FStar_List.for_all
                                  (fun uu____17511  ->
                                     match uu____17511 with
                                     | (uu____17525,uu____17526,e') ->
                                         let uu____17540 = simp_t e'  in
                                         uu____17540 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____17492
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____17556 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____17566 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____17566
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____17604 =
                 match uu____17604 with
                 | (t1,q) ->
                     let uu____17625 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____17625 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____17657 -> (t1, q))
                  in
               let uu____17670 = FStar_Syntax_Util.head_and_args t  in
               match uu____17670 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____17750 =
                 let uu____17751 = FStar_Syntax_Util.unmeta ty  in
                 uu____17751.FStar_Syntax_Syntax.n  in
               match uu____17750 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____17756) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____17761,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____17785 -> false  in
             let simplify1 arg =
               let uu____17818 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____17818, arg)  in
             let uu____17833 = is_forall_const tm1  in
             match uu____17833 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____17839 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____17841 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____17839
                       uu____17841)
                  else ();
                  (let uu____17846 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____17846))
             | FStar_Pervasives_Native.None  ->
                 let uu____17847 =
                   let uu____17848 = FStar_Syntax_Subst.compress tm1  in
                   uu____17848.FStar_Syntax_Syntax.n  in
                 (match uu____17847 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____17852;
                              FStar_Syntax_Syntax.vars = uu____17853;_},uu____17854);
                         FStar_Syntax_Syntax.pos = uu____17855;
                         FStar_Syntax_Syntax.vars = uu____17856;_},args)
                      ->
                      let uu____17886 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17886
                      then
                        let uu____17889 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17889 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17947)::
                             (uu____17948,(arg,uu____17950))::[] ->
                             maybe_auto_squash arg
                         | (uu____18023,(arg,uu____18025))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____18026)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____18099)::uu____18100::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____18170::(FStar_Pervasives_Native.Some (false
                                         ),uu____18171)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____18241 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____18259 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____18259
                         then
                           let uu____18262 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____18262 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____18320)::uu____18321::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____18391::(FStar_Pervasives_Native.Some (true
                                           ),uu____18392)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18462)::(uu____18463,(arg,uu____18465))::[]
                               -> maybe_auto_squash arg
                           | (uu____18538,(arg,uu____18540))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18541)::[]
                               -> maybe_auto_squash arg
                           | uu____18614 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18632 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18632
                            then
                              let uu____18635 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18635 with
                              | uu____18693::(FStar_Pervasives_Native.Some
                                              (true ),uu____18694)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18764)::uu____18765::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18835)::(uu____18836,(arg,uu____18838))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18911,(p,uu____18913))::(uu____18914,
                                                                (q,uu____18916))::[]
                                  ->
                                  let uu____18988 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18988
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18993 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____19011 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____19011
                               then
                                 let uu____19014 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____19014 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19072)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19073)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19147)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19148)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19222)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____19223)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19297)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____19298)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____19372,(arg,uu____19374))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____19375)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____19448)::(uu____19449,(arg,uu____19451))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19524,(arg,uu____19526))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19527)::[]
                                     ->
                                     let uu____19600 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19600
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19601)::(uu____19602,(arg,uu____19604))::[]
                                     ->
                                     let uu____19677 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19677
                                 | (uu____19678,(p,uu____19680))::(uu____19681,
                                                                   (q,uu____19683))::[]
                                     ->
                                     let uu____19755 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19755
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19760 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19778 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19778
                                  then
                                    let uu____19781 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19781 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19839)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19883)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19927 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19945 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19945
                                     then
                                       match args with
                                       | (t,uu____19949)::[] ->
                                           let uu____19974 =
                                             let uu____19975 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19975.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19974 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19978::[],body,uu____19980)
                                                ->
                                                let uu____20015 = simp_t body
                                                   in
                                                (match uu____20015 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____20021 -> tm1)
                                            | uu____20025 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____20027))::(t,uu____20029)::[]
                                           ->
                                           let uu____20069 =
                                             let uu____20070 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____20070.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____20069 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____20073::[],body,uu____20075)
                                                ->
                                                let uu____20110 = simp_t body
                                                   in
                                                (match uu____20110 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____20118 -> tm1)
                                            | uu____20122 -> tm1)
                                       | uu____20123 -> tm1
                                     else
                                       (let uu____20136 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____20136
                                        then
                                          match args with
                                          | (t,uu____20140)::[] ->
                                              let uu____20165 =
                                                let uu____20166 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20166.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20165 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20169::[],body,uu____20171)
                                                   ->
                                                   let uu____20206 =
                                                     simp_t body  in
                                                   (match uu____20206 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____20212 -> tm1)
                                               | uu____20216 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____20218))::(t,uu____20220)::[]
                                              ->
                                              let uu____20260 =
                                                let uu____20261 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____20261.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____20260 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____20264::[],body,uu____20266)
                                                   ->
                                                   let uu____20301 =
                                                     simp_t body  in
                                                   (match uu____20301 with
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
                                                    | uu____20309 -> tm1)
                                               | uu____20313 -> tm1)
                                          | uu____20314 -> tm1
                                        else
                                          (let uu____20327 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____20327
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20330;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20331;_},uu____20332)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____20358;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____20359;_},uu____20360)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____20386 -> tm1
                                           else
                                             (let uu____20399 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____20399
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____20413 =
                                                    let uu____20414 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____20414.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____20413 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____20425 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____20439 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____20439
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____20478 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____20478
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____20484 =
                                                         let uu____20485 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____20485.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____20484 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____20488 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____20496 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____20496
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____20505
                                                                  =
                                                                  let uu____20506
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____20506.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____20505
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____20512)
                                                                    -> hd1
                                                                | uu____20537
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____20541
                                                                =
                                                                let uu____20552
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____20552]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____20541)
                                                       | uu____20585 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____20590 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____20590 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____20610 ->
                                                     let uu____20619 =
                                                       let uu____20626 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____20626 cfg env
                                                        in
                                                     uu____20619 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20632;
                         FStar_Syntax_Syntax.vars = uu____20633;_},args)
                      ->
                      let uu____20659 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20659
                      then
                        let uu____20662 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20662 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20720)::
                             (uu____20721,(arg,uu____20723))::[] ->
                             maybe_auto_squash arg
                         | (uu____20796,(arg,uu____20798))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20799)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20872)::uu____20873::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20943::(FStar_Pervasives_Native.Some (false
                                         ),uu____20944)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____21014 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____21032 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____21032
                         then
                           let uu____21035 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____21035 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____21093)::uu____21094::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____21164::(FStar_Pervasives_Native.Some (true
                                           ),uu____21165)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____21235)::(uu____21236,(arg,uu____21238))::[]
                               -> maybe_auto_squash arg
                           | (uu____21311,(arg,uu____21313))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____21314)::[]
                               -> maybe_auto_squash arg
                           | uu____21387 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____21405 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____21405
                            then
                              let uu____21408 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____21408 with
                              | uu____21466::(FStar_Pervasives_Native.Some
                                              (true ),uu____21467)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21537)::uu____21538::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21608)::(uu____21609,(arg,uu____21611))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21684,(p,uu____21686))::(uu____21687,
                                                                (q,uu____21689))::[]
                                  ->
                                  let uu____21761 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21761
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21766 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21784 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21784
                               then
                                 let uu____21787 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21787 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21845)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21846)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21920)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21921)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21995)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21996)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22070)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____22071)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____22145,(arg,uu____22147))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____22148)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____22221)::(uu____22222,(arg,uu____22224))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____22297,(arg,uu____22299))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____22300)::[]
                                     ->
                                     let uu____22373 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22373
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____22374)::(uu____22375,(arg,uu____22377))::[]
                                     ->
                                     let uu____22450 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____22450
                                 | (uu____22451,(p,uu____22453))::(uu____22454,
                                                                   (q,uu____22456))::[]
                                     ->
                                     let uu____22528 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22528
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22533 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22551 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22551
                                  then
                                    let uu____22554 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22554 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22612)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22656)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22700 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22718 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22718
                                     then
                                       match args with
                                       | (t,uu____22722)::[] ->
                                           let uu____22747 =
                                             let uu____22748 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22748.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22747 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22751::[],body,uu____22753)
                                                ->
                                                let uu____22788 = simp_t body
                                                   in
                                                (match uu____22788 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22794 -> tm1)
                                            | uu____22798 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22800))::(t,uu____22802)::[]
                                           ->
                                           let uu____22842 =
                                             let uu____22843 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22843.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22842 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22846::[],body,uu____22848)
                                                ->
                                                let uu____22883 = simp_t body
                                                   in
                                                (match uu____22883 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22891 -> tm1)
                                            | uu____22895 -> tm1)
                                       | uu____22896 -> tm1
                                     else
                                       (let uu____22909 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22909
                                        then
                                          match args with
                                          | (t,uu____22913)::[] ->
                                              let uu____22938 =
                                                let uu____22939 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22939.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22938 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22942::[],body,uu____22944)
                                                   ->
                                                   let uu____22979 =
                                                     simp_t body  in
                                                   (match uu____22979 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22985 -> tm1)
                                               | uu____22989 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22991))::(t,uu____22993)::[]
                                              ->
                                              let uu____23033 =
                                                let uu____23034 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____23034.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____23033 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____23037::[],body,uu____23039)
                                                   ->
                                                   let uu____23074 =
                                                     simp_t body  in
                                                   (match uu____23074 with
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
                                                    | uu____23082 -> tm1)
                                               | uu____23086 -> tm1)
                                          | uu____23087 -> tm1
                                        else
                                          (let uu____23100 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____23100
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23103;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23104;_},uu____23105)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____23131;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____23132;_},uu____23133)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____23159 -> tm1
                                           else
                                             (let uu____23172 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____23172
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____23186 =
                                                    let uu____23187 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____23187.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____23186 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____23198 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     Prims.int_one
                                                 then
                                                   let t =
                                                     let uu____23212 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____23212
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____23247 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____23247
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____23253 =
                                                         let uu____23254 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____23254.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____23253 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____23257 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____23265 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____23265
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____23274
                                                                  =
                                                                  let uu____23275
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____23275.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____23274
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____23281)
                                                                    -> hd1
                                                                | uu____23306
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____23310
                                                                =
                                                                let uu____23321
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____23321]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____23310)
                                                       | uu____23354 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____23359 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____23359 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____23379 ->
                                                     let uu____23388 =
                                                       let uu____23395 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____23395 cfg env
                                                        in
                                                     uu____23388 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____23406 = simp_t t  in
                      (match uu____23406 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____23415 ->
                      let uu____23438 = is_const_match tm1  in
                      (match uu____23438 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____23447 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____23457  ->
               (let uu____23459 = FStar_Syntax_Print.tag_of_term t  in
                let uu____23461 = FStar_Syntax_Print.term_to_string t  in
                let uu____23463 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____23471 =
                  let uu____23473 =
                    let uu____23476 = firstn (Prims.of_int (4)) stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____23476
                     in
                  stack_to_string uu____23473  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____23459 uu____23461 uu____23463 uu____23471);
               (let uu____23501 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____23501
                then
                  let uu____23505 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____23505 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____23512 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____23514 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____23516 =
                          let uu____23518 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____23518
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____23512
                          uu____23514 uu____23516);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____23540 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____23548)::uu____23549 -> true
                | uu____23559 -> false)
              in
           if uu____23540
           then
             let uu____23562 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____23562 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____23576 =
                        let uu____23578 =
                          let uu____23580 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____23580  in
                        FStar_Util.string_of_int uu____23578  in
                      let uu____23587 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____23589 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____23576 uu____23587 uu____23589)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____23598,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____23627  ->
                        let uu____23628 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____23628);
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
                  let uu____23671 =
                    let uu___2783_23672 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2783_23672.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2783_23672.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____23671
              | (Arg (Univ uu____23675,uu____23676,uu____23677))::uu____23678
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____23682,uu____23683))::uu____23684 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____23700,uu____23701),aq,r))::stack1
                  when
                  let uu____23753 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____23753 ->
                  let t2 =
                    let uu____23757 =
                      let uu____23762 =
                        let uu____23763 = closure_as_term cfg env_arg tm  in
                        (uu____23763, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____23762  in
                    uu____23757 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____23773),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____23828  ->
                        let uu____23829 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____23829);
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
                     (let uu____23849 = FStar_ST.op_Bang m  in
                      match uu____23849 with
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
                      | FStar_Pervasives_Native.Some (uu____23937,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____23993 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____23998  ->
                         let uu____23999 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____23999);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____24009 =
                    let uu____24010 = FStar_Syntax_Subst.compress t1  in
                    uu____24010.FStar_Syntax_Syntax.n  in
                  (match uu____24009 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____24038 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____24038  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____24042  ->
                             let uu____24043 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____24043);
                        (let uu____24046 = FStar_List.tl stack  in
                         norm cfg env1 uu____24046 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____24047);
                          FStar_Syntax_Syntax.pos = uu____24048;
                          FStar_Syntax_Syntax.vars = uu____24049;_},(uu____24050,FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu____24051))::
                        (e,uu____24053)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____24107 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____24124 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____24124 with
                        | (hd1,args) ->
                            let uu____24167 =
                              let uu____24168 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____24168.FStar_Syntax_Syntax.n  in
                            (match uu____24167 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____24172 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____24172 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____24175;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____24176;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____24177;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____24179;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____24180;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____24181;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____24182;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____24218 -> fallback " (3)" ())
                             | uu____24222 -> fallback " (4)" ()))
                   | uu____24224 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____24250  ->
                        let uu____24251 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____24251);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____24262 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____24267  ->
                           let uu____24268 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____24270 =
                             let uu____24272 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____24302  ->
                                       match uu____24302 with
                                       | (p,uu____24313,uu____24314) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____24272
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____24268 uu____24270);
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
                                (fun uu___17_24336  ->
                                   match uu___17_24336 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____24340 -> false))
                            in
                         let steps =
                           let uu___2956_24343 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___2956_24343.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___2959_24350 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___2959_24350.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___2959_24350.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___2959_24350.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___2959_24350.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___2959_24350.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___2959_24350.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____24425 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____24456 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____24545  ->
                                       fun uu____24546  ->
                                         match (uu____24545, uu____24546)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____24696 =
                                               norm_pat env3 p1  in
                                             (match uu____24696 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____24456 with
                              | (pats1,env3) ->
                                  ((let uu___2987_24866 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___2987_24866.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___2991_24887 = x  in
                               let uu____24888 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2991_24887.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2991_24887.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24888
                               }  in
                             ((let uu___2994_24902 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___2994_24902.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___2998_24913 = x  in
                               let uu____24914 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2998_24913.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2998_24913.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24914
                               }  in
                             ((let uu___3001_24928 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___3001_24928.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___3007_24944 = x  in
                               let uu____24945 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___3007_24944.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___3007_24944.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24945
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___3011_24960 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___3011_24960.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____25004 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____25034 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____25034 with
                                     | (p,wopt,e) ->
                                         let uu____25054 = norm_pat env1 p
                                            in
                                         (match uu____25054 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____25109 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____25109
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____25126 =
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
                         if uu____25126
                         then
                           norm
                             (let uu___3030_25133 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___3032_25136 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___3032_25136.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___3030_25133.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___3030_25133.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___3030_25133.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___3030_25133.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___3030_25133.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___3030_25133.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___3030_25133.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___3030_25133.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____25140 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____25140)
                       in
                    let rec is_cons head1 =
                      let uu____25166 =
                        let uu____25167 = FStar_Syntax_Subst.compress head1
                           in
                        uu____25167.FStar_Syntax_Syntax.n  in
                      match uu____25166 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____25172) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____25177 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____25179;
                            FStar_Syntax_Syntax.fv_delta = uu____25180;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____25182;
                            FStar_Syntax_Syntax.fv_delta = uu____25183;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____25184);_}
                          -> true
                      | uu____25192 -> false  in
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
                      let uu____25361 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____25361 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____25458 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____25500 ->
                                    let uu____25501 =
                                      let uu____25503 = is_cons head1  in
                                      Prims.op_Negation uu____25503  in
                                    FStar_Util.Inr uu____25501)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____25532 =
                                 let uu____25533 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____25533.FStar_Syntax_Syntax.n  in
                               (match uu____25532 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____25552 ->
                                    let uu____25553 =
                                      let uu____25555 = is_cons head1  in
                                      Prims.op_Negation uu____25555  in
                                    FStar_Util.Inr uu____25553))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____25646)::rest_a,(p1,uu____25649)::rest_p)
                          ->
                          let uu____25708 = matches_pat t2 p1  in
                          (match uu____25708 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____25761 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____25884 = matches_pat scrutinee1 p1  in
                          (match uu____25884 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____25930  ->
                                     let uu____25931 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____25933 =
                                       let uu____25935 =
                                         FStar_List.map
                                           (fun uu____25947  ->
                                              match uu____25947 with
                                              | (uu____25953,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____25935
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____25931 uu____25933);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____25989  ->
                                          match uu____25989 with
                                          | (bv,t2) ->
                                              let uu____26012 =
                                                let uu____26019 =
                                                  let uu____26022 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____26022
                                                   in
                                                let uu____26023 =
                                                  let uu____26024 =
                                                    let uu____26056 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____26056,
                                                      false)
                                                     in
                                                  Clos uu____26024  in
                                                (uu____26019, uu____26023)
                                                 in
                                              uu____26012 :: env2) env1 s
                                    in
                                 let uu____26149 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____26149)))
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
            (fun uu____26182  ->
               let uu____26183 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____26183);
          (let uu____26186 = is_nbe_request s  in
           if uu____26186
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____26192  ->
                   let uu____26193 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____26193);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____26199  ->
                   let uu____26200 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26200);
              (let uu____26203 =
                 FStar_Util.record_time (fun uu____26210  -> nbe_eval c s t)
                  in
               match uu____26203 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26219  ->
                         let uu____26220 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26222 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26220 uu____26222);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____26230  ->
                   let uu____26231 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____26231);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____26237  ->
                   let uu____26238 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____26238);
              (let uu____26241 =
                 FStar_Util.record_time (fun uu____26248  -> norm c [] [] t)
                  in
               match uu____26241 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____26263  ->
                         let uu____26264 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____26266 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____26264 uu____26266);
                    r))))
  
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s  -> fun e  -> fun t  -> normalize_with_primitive_steps [] s e t 
let (normalize_comp :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun s  ->
    fun e  ->
      fun t  ->
        let uu____26301 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____26301 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____26319 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____26319 [] u
  
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
        let uu____26345 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____26345  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____26352 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3188_26371 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3188_26371.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3188_26371.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____26378 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____26378
          then
            let ct1 =
              let uu____26382 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____26382 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____26389 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____26389
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3198_26396 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3198_26396.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3198_26396.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3198_26396.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___3202_26398 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3202_26398.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3202_26398.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3202_26398.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3202_26398.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3205_26399 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3205_26399.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3205_26399.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____26402 -> c
  
let (ghost_to_pure_lcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp)
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
        let uu____26422 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____26422  in
      let uu____26429 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____26429
      then
        let uu____26432 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____26432 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____26438  ->
                 let uu____26439 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____26439)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3221_26456  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3220_26459 ->
            ((let uu____26461 =
                let uu____26467 =
                  let uu____26469 = FStar_Util.message_of_exn uu___3220_26459
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26469
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26467)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____26461);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3231_26488  ->
             match () with
             | () ->
                 let uu____26489 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____26489 [] c) ()
        with
        | uu___3230_26498 ->
            ((let uu____26500 =
                let uu____26506 =
                  let uu____26508 = FStar_Util.message_of_exn uu___3230_26498
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26508
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26506)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____26500);
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
                   let uu____26557 =
                     let uu____26558 =
                       let uu____26565 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____26565)  in
                     FStar_Syntax_Syntax.Tm_refine uu____26558  in
                   mk uu____26557 t01.FStar_Syntax_Syntax.pos
               | uu____26570 -> t2)
          | uu____26571 -> t2  in
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
        let uu____26665 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____26665 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____26702 ->
                 let uu____26711 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____26711 with
                  | (actuals,uu____26721,uu____26722) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____26742 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____26742 with
                         | (binders,args) ->
                             let uu____26753 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____26753
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
      | uu____26768 ->
          let uu____26769 = FStar_Syntax_Util.head_and_args t  in
          (match uu____26769 with
           | (head1,args) ->
               let uu____26812 =
                 let uu____26813 = FStar_Syntax_Subst.compress head1  in
                 uu____26813.FStar_Syntax_Syntax.n  in
               (match uu____26812 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____26834 =
                      let uu____26849 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____26849  in
                    (match uu____26834 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____26889 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3301_26897 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3301_26897.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3301_26897.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3301_26897.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3301_26897.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3301_26897.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3301_26897.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3301_26897.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3301_26897.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3301_26897.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3301_26897.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3301_26897.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3301_26897.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3301_26897.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3301_26897.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3301_26897.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3301_26897.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3301_26897.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3301_26897.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3301_26897.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3301_26897.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3301_26897.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3301_26897.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3301_26897.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3301_26897.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3301_26897.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3301_26897.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3301_26897.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3301_26897.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3301_26897.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3301_26897.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3301_26897.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3301_26897.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3301_26897.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3301_26897.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3301_26897.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3301_26897.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3301_26897.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3301_26897.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3301_26897.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3301_26897.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___3301_26897.FStar_TypeChecker_Env.strict_args_tab)
                                 }) t
                               in
                            match uu____26889 with
                            | (uu____26900,ty,uu____26902) ->
                                eta_expand_with_type env t ty))
                | uu____26903 ->
                    let uu____26904 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3308_26912 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3308_26912.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3308_26912.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3308_26912.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3308_26912.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3308_26912.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3308_26912.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3308_26912.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3308_26912.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3308_26912.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3308_26912.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3308_26912.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3308_26912.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3308_26912.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3308_26912.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3308_26912.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3308_26912.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3308_26912.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3308_26912.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3308_26912.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3308_26912.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3308_26912.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3308_26912.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3308_26912.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3308_26912.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3308_26912.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3308_26912.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3308_26912.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3308_26912.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3308_26912.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3308_26912.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3308_26912.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3308_26912.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3308_26912.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3308_26912.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3308_26912.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3308_26912.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3308_26912.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3308_26912.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3308_26912.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3308_26912.FStar_TypeChecker_Env.nbe);
                           FStar_TypeChecker_Env.strict_args_tab =
                             (uu___3308_26912.FStar_TypeChecker_Env.strict_args_tab)
                         }) t
                       in
                    (match uu____26904 with
                     | (uu____26915,ty,uu____26917) ->
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
      let uu___3320_26999 = x  in
      let uu____27000 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3320_26999.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3320_26999.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____27000
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____27003 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____27027 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____27028 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____27029 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____27030 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____27037 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____27038 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____27039 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3346_27073 = rc  in
          let uu____27074 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____27083 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3346_27073.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____27074;
            FStar_Syntax_Syntax.residual_flags = uu____27083
          }  in
        let uu____27086 =
          let uu____27087 =
            let uu____27106 = elim_delayed_subst_binders bs  in
            let uu____27115 = elim_delayed_subst_term t2  in
            let uu____27118 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____27106, uu____27115, uu____27118)  in
          FStar_Syntax_Syntax.Tm_abs uu____27087  in
        mk1 uu____27086
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____27155 =
          let uu____27156 =
            let uu____27171 = elim_delayed_subst_binders bs  in
            let uu____27180 = elim_delayed_subst_comp c  in
            (uu____27171, uu____27180)  in
          FStar_Syntax_Syntax.Tm_arrow uu____27156  in
        mk1 uu____27155
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____27199 =
          let uu____27200 =
            let uu____27207 = elim_bv bv  in
            let uu____27208 = elim_delayed_subst_term phi  in
            (uu____27207, uu____27208)  in
          FStar_Syntax_Syntax.Tm_refine uu____27200  in
        mk1 uu____27199
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____27239 =
          let uu____27240 =
            let uu____27257 = elim_delayed_subst_term t2  in
            let uu____27260 = elim_delayed_subst_args args  in
            (uu____27257, uu____27260)  in
          FStar_Syntax_Syntax.Tm_app uu____27240  in
        mk1 uu____27239
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3368_27332 = p  in
              let uu____27333 =
                let uu____27334 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____27334  in
              {
                FStar_Syntax_Syntax.v = uu____27333;
                FStar_Syntax_Syntax.p =
                  (uu___3368_27332.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3372_27336 = p  in
              let uu____27337 =
                let uu____27338 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____27338  in
              {
                FStar_Syntax_Syntax.v = uu____27337;
                FStar_Syntax_Syntax.p =
                  (uu___3372_27336.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3378_27345 = p  in
              let uu____27346 =
                let uu____27347 =
                  let uu____27354 = elim_bv x  in
                  let uu____27355 = elim_delayed_subst_term t0  in
                  (uu____27354, uu____27355)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____27347  in
              {
                FStar_Syntax_Syntax.v = uu____27346;
                FStar_Syntax_Syntax.p =
                  (uu___3378_27345.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3384_27380 = p  in
              let uu____27381 =
                let uu____27382 =
                  let uu____27396 =
                    FStar_List.map
                      (fun uu____27422  ->
                         match uu____27422 with
                         | (x,b) ->
                             let uu____27439 = elim_pat x  in
                             (uu____27439, b)) pats
                     in
                  (fv, uu____27396)  in
                FStar_Syntax_Syntax.Pat_cons uu____27382  in
              {
                FStar_Syntax_Syntax.v = uu____27381;
                FStar_Syntax_Syntax.p =
                  (uu___3384_27380.FStar_Syntax_Syntax.p)
              }
          | uu____27454 -> p  in
        let elim_branch uu____27478 =
          match uu____27478 with
          | (pat,wopt,t3) ->
              let uu____27504 = elim_pat pat  in
              let uu____27507 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____27510 = elim_delayed_subst_term t3  in
              (uu____27504, uu____27507, uu____27510)
           in
        let uu____27515 =
          let uu____27516 =
            let uu____27539 = elim_delayed_subst_term t2  in
            let uu____27542 = FStar_List.map elim_branch branches  in
            (uu____27539, uu____27542)  in
          FStar_Syntax_Syntax.Tm_match uu____27516  in
        mk1 uu____27515
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____27673 =
          match uu____27673 with
          | (tc,topt) ->
              let uu____27708 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____27718 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____27718
                | FStar_Util.Inr c ->
                    let uu____27720 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____27720
                 in
              let uu____27721 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____27708, uu____27721)
           in
        let uu____27730 =
          let uu____27731 =
            let uu____27758 = elim_delayed_subst_term t2  in
            let uu____27761 = elim_ascription a  in
            (uu____27758, uu____27761, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____27731  in
        mk1 uu____27730
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3414_27824 = lb  in
          let uu____27825 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____27828 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3414_27824.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3414_27824.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____27825;
            FStar_Syntax_Syntax.lbeff =
              (uu___3414_27824.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____27828;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3414_27824.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3414_27824.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____27831 =
          let uu____27832 =
            let uu____27846 =
              let uu____27854 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____27854)  in
            let uu____27866 = elim_delayed_subst_term t2  in
            (uu____27846, uu____27866)  in
          FStar_Syntax_Syntax.Tm_let uu____27832  in
        mk1 uu____27831
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____27911 =
          let uu____27912 =
            let uu____27919 = elim_delayed_subst_term tm  in
            (uu____27919, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____27912  in
        mk1 uu____27911
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____27930 =
          let uu____27931 =
            let uu____27938 = elim_delayed_subst_term t2  in
            let uu____27941 = elim_delayed_subst_meta md  in
            (uu____27938, uu____27941)  in
          FStar_Syntax_Syntax.Tm_meta uu____27931  in
        mk1 uu____27930

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___18_27950  ->
         match uu___18_27950 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____27954 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____27954
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
        let uu____27977 =
          let uu____27978 =
            let uu____27987 = elim_delayed_subst_term t  in
            (uu____27987, uopt)  in
          FStar_Syntax_Syntax.Total uu____27978  in
        mk1 uu____27977
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____28004 =
          let uu____28005 =
            let uu____28014 = elim_delayed_subst_term t  in
            (uu____28014, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____28005  in
        mk1 uu____28004
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3447_28023 = ct  in
          let uu____28024 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____28027 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____28038 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3447_28023.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3447_28023.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____28024;
            FStar_Syntax_Syntax.effect_args = uu____28027;
            FStar_Syntax_Syntax.flags = uu____28038
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___19_28041  ->
    match uu___19_28041 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args) ->
        let uu____28076 =
          let uu____28097 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____28106 = FStar_List.map elim_delayed_subst_args args  in
          (uu____28097, uu____28106)  in
        FStar_Syntax_Syntax.Meta_pattern uu____28076
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____28161 =
          let uu____28168 = elim_delayed_subst_term t  in (m, uu____28168)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____28161
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____28180 =
          let uu____28189 = elim_delayed_subst_term t  in
          (m1, m2, uu____28189)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____28180
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
      (fun uu____28222  ->
         match uu____28222 with
         | (t,q) ->
             let uu____28241 = elim_delayed_subst_term t  in (uu____28241, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____28269  ->
         match uu____28269 with
         | (x,q) ->
             let uu____28288 =
               let uu___3473_28289 = x  in
               let uu____28290 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3473_28289.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3473_28289.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____28290
               }  in
             (uu____28288, q)) bs

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
            | (uu____28398,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____28430,FStar_Util.Inl t) ->
                let uu____28452 =
                  let uu____28459 =
                    let uu____28460 =
                      let uu____28475 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____28475)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____28460  in
                  FStar_Syntax_Syntax.mk uu____28459  in
                uu____28452 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____28488 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____28488 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____28520 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____28593 ->
                    let uu____28594 =
                      let uu____28603 =
                        let uu____28604 = FStar_Syntax_Subst.compress t4  in
                        uu____28604.FStar_Syntax_Syntax.n  in
                      (uu____28603, tc)  in
                    (match uu____28594 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____28633) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____28680) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____28725,FStar_Util.Inl uu____28726) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____28757 -> failwith "Impossible")
                 in
              (match uu____28520 with
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
          let uu____28896 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____28896 with
          | (univ_names1,binders1,tc) ->
              let uu____28970 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____28970)
  
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
          let uu____29024 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____29024 with
          | (univ_names1,binders1,tc) ->
              let uu____29098 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____29098)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____29140 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____29140 with
           | (univ_names1,binders1,typ1) ->
               let uu___3556_29180 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3556_29180.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3556_29180.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3556_29180.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3556_29180.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3562_29195 = s  in
          let uu____29196 =
            let uu____29197 =
              let uu____29206 = FStar_List.map (elim_uvars env) sigs  in
              (uu____29206, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____29197  in
          {
            FStar_Syntax_Syntax.sigel = uu____29196;
            FStar_Syntax_Syntax.sigrng =
              (uu___3562_29195.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3562_29195.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3562_29195.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3562_29195.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____29225 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29225 with
           | (univ_names1,uu____29249,typ1) ->
               let uu___3576_29271 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3576_29271.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3576_29271.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3576_29271.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3576_29271.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____29278 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____29278 with
           | (univ_names1,uu____29302,typ1) ->
               let uu___3587_29324 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3587_29324.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3587_29324.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3587_29324.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3587_29324.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____29354 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____29354 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____29379 =
                            let uu____29380 =
                              let uu____29381 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____29381  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____29380
                             in
                          elim_delayed_subst_term uu____29379  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3603_29384 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3603_29384.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3603_29384.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3603_29384.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3603_29384.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3606_29385 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3606_29385.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3606_29385.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3606_29385.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3606_29385.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3610_29392 = s  in
          let uu____29393 =
            let uu____29394 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____29394  in
          {
            FStar_Syntax_Syntax.sigel = uu____29393;
            FStar_Syntax_Syntax.sigrng =
              (uu___3610_29392.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3610_29392.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3610_29392.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3610_29392.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____29398 = elim_uvars_aux_t env us [] t  in
          (match uu____29398 with
           | (us1,uu____29422,t1) ->
               let uu___3621_29444 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3621_29444.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3621_29444.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3621_29444.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3621_29444.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let signature = ed.FStar_Syntax_Syntax.signature  in
          let uu____29447 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders signature
             in
          (match uu____29447 with
           | (univs1,binders,signature1) ->
               let uu____29487 =
                 let uu____29492 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____29492 with
                 | (univs_opening,univs2) ->
                     let uu____29515 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____29515)
                  in
               (match uu____29487 with
                | (univs_opening,univs_closing) ->
                    let uu____29518 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____29524 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____29525 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____29524, uu____29525)  in
                    (match uu____29518 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____29551 =
                           match uu____29551 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____29569 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____29569 with
                                | (us1,t1) ->
                                    let uu____29580 =
                                      let uu____29589 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____29594 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____29589, uu____29594)  in
                                    (match uu____29580 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____29617 =
                                           let uu____29626 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____29631 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____29626, uu____29631)  in
                                         (match uu____29617 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____29655 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____29655
                                                 in
                                              let uu____29656 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____29656 with
                                               | (uu____29683,uu____29684,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____29707 =
                                                       let uu____29708 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____29708
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____29707
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____29717 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____29717 with
                           | (uu____29736,uu____29737,t1) -> t1  in
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
                             | uu____29813 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____29840 =
                               let uu____29841 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____29841.FStar_Syntax_Syntax.n  in
                             match uu____29840 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____29900 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____29934 =
                               let uu____29935 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____29935.FStar_Syntax_Syntax.n  in
                             match uu____29934 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____29958) ->
                                 let uu____29983 = destruct_action_body body
                                    in
                                 (match uu____29983 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____30032 ->
                                 let uu____30033 = destruct_action_body t  in
                                 (match uu____30033 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____30088 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____30088 with
                           | (action_univs,t) ->
                               let uu____30097 = destruct_action_typ_templ t
                                  in
                               (match uu____30097 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3706_30144 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3706_30144.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3706_30144.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3709_30146 = ed  in
                           let uu____30147 =
                             let uu____30148 =
                               elim_term
                                 (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m
                                in
                             let uu____30149 =
                               elim_tscheme
                                 (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                in
                             let uu____30150 =
                               elim_tscheme
                                 (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                in
                             {
                               FStar_Syntax_Syntax.monad_m = uu____30148;
                               FStar_Syntax_Syntax.monad_ret = uu____30149;
                               FStar_Syntax_Syntax.monad_bind = uu____30150
                             }  in
                           let uu____30151 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____30152 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____30153 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____30154 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____30155 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____30156 =
                             let uu____30157 =
                               elim_term
                                 (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                                in
                             let uu____30158 =
                               elim_tscheme
                                 (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                in
                             let uu____30159 =
                               elim_tscheme
                                 (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                in
                             {
                               FStar_Syntax_Syntax.monad_m = uu____30157;
                               FStar_Syntax_Syntax.monad_ret = uu____30158;
                               FStar_Syntax_Syntax.monad_bind = uu____30159
                             }  in
                           let uu____30160 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3709_30146.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___3709_30146.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.spec = uu____30147;
                             FStar_Syntax_Syntax.signature = signature1;
                             FStar_Syntax_Syntax.if_then_else = uu____30151;
                             FStar_Syntax_Syntax.ite_wp = uu____30152;
                             FStar_Syntax_Syntax.stronger = uu____30153;
                             FStar_Syntax_Syntax.close_wp = uu____30154;
                             FStar_Syntax_Syntax.trivial = uu____30155;
                             FStar_Syntax_Syntax.repr = uu____30156;
                             FStar_Syntax_Syntax.elaborated =
                               (uu___3709_30146.FStar_Syntax_Syntax.elaborated);
                             FStar_Syntax_Syntax.spec_dm4f =
                               (uu___3709_30146.FStar_Syntax_Syntax.spec_dm4f);
                             FStar_Syntax_Syntax.interp =
                               (uu___3709_30146.FStar_Syntax_Syntax.interp);
                             FStar_Syntax_Syntax.mrelation =
                               (uu___3709_30146.FStar_Syntax_Syntax.mrelation);
                             FStar_Syntax_Syntax.actions = uu____30160;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3709_30146.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3712_30163 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3712_30163.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3712_30163.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3712_30163.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3712_30163.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___20_30184 =
            match uu___20_30184 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____30215 = elim_uvars_aux_t env us [] t  in
                (match uu____30215 with
                 | (us1,uu____30247,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3727_30278 = sub_eff  in
            let uu____30279 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____30282 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3727_30278.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3727_30278.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____30279;
              FStar_Syntax_Syntax.lift = uu____30282
            }  in
          let uu___3730_30285 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3730_30285.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3730_30285.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3730_30285.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3730_30285.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____30295 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____30295 with
           | (univ_names1,binders1,comp1) ->
               let uu___3743_30335 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3743_30335.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3743_30335.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3743_30335.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3743_30335.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____30338 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____30339 -> s
  
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
        let uu____30388 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____30388 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____30410 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____30410 with
             | (uu____30417,head_def) ->
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
      let uu____30423 = FStar_Syntax_Util.head_and_args t  in
      match uu____30423 with
      | (head1,args) ->
          let uu____30468 =
            let uu____30469 = FStar_Syntax_Subst.compress head1  in
            uu____30469.FStar_Syntax_Syntax.n  in
          (match uu____30468 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____30476;
                  FStar_Syntax_Syntax.vars = uu____30477;_},us)
               -> aux fv us args
           | uu____30483 -> FStar_Pervasives_Native.None)
  