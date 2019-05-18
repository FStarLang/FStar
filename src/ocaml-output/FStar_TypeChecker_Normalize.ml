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
                 | FStar_Syntax_Syntax.Meta_pattern (names1,args,np) ->
                     let uu____4229 =
                       let uu____4253 =
                         FStar_All.pipe_right names1
                           (FStar_List.map
                              (non_tail_inline_closure_env cfg env_m))
                          in
                       let uu____4270 =
                         FStar_All.pipe_right args
                           (FStar_List.map
                              (fun args1  ->
                                 FStar_All.pipe_right args1
                                   (FStar_List.map
                                      (fun uu____4379  ->
                                         match uu____4379 with
                                         | (a,q) ->
                                             let uu____4406 =
                                               non_tail_inline_closure_env
                                                 cfg env_m a
                                                in
                                             (uu____4406, q)))))
                          in
                       (uu____4253, uu____4270, np)  in
                     FStar_Syntax_Syntax.Meta_pattern uu____4229
                 | FStar_Syntax_Syntax.Meta_monadic (m1,tbody) ->
                     let uu____4436 =
                       let uu____4443 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, uu____4443)  in
                     FStar_Syntax_Syntax.Meta_monadic uu____4436
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,tbody) ->
                     let uu____4455 =
                       let uu____4464 =
                         non_tail_inline_closure_env cfg env_m tbody  in
                       (m1, m2, uu____4464)  in
                     FStar_Syntax_Syntax.Meta_monadic_lift uu____4455
                 | uu____4469 -> m  in
               let t1 = mk (FStar_Syntax_Syntax.Tm_meta (t, m1)) r  in
               rebuild_closure cfg env stack1 t1
           | uu____4475 -> failwith "Impossible: unexpected stack element")

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
            let uu____4491 =
              let uu____4492 = inline_closure_env cfg env [] t  in
              FStar_Syntax_Syntax.Meta uu____4492  in
            FStar_Pervasives_Native.Some uu____4491
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
        let uu____4509 =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun uu____4593  ->
                  fun uu____4594  ->
                    match (uu____4593, uu____4594) with
                    | ((env1,out),(b,imp)) ->
                        let b1 =
                          let uu___566_4734 = b  in
                          let uu____4735 =
                            inline_closure_env cfg env1 []
                              b.FStar_Syntax_Syntax.sort
                             in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___566_4734.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___566_4734.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = uu____4735
                          }  in
                        let imp1 = close_imp cfg env1 imp  in
                        let env2 = dummy :: env1  in
                        (env2, ((b1, imp1) :: out))) (env, []))
           in
        match uu____4509 with | (env1,bs1) -> ((FStar_List.rev bs1), env1)

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
        | uu____4877 ->
            (match c.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Total (t,uopt) ->
                 let uu____4890 = inline_closure_env cfg env [] t  in
                 let uu____4891 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_Total' uu____4890 uu____4891
             | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                 let uu____4904 = inline_closure_env cfg env [] t  in
                 let uu____4905 =
                   FStar_Option.map (norm_universe cfg env) uopt  in
                 FStar_Syntax_Syntax.mk_GTotal' uu____4904 uu____4905
             | FStar_Syntax_Syntax.Comp c1 ->
                 let rt =
                   inline_closure_env cfg env []
                     c1.FStar_Syntax_Syntax.result_typ
                    in
                 let args =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.effect_args
                     (FStar_List.map
                        (fun uu____4959  ->
                           match uu____4959 with
                           | (a,q) ->
                               let uu____4980 =
                                 inline_closure_env cfg env [] a  in
                               (uu____4980, q)))
                    in
                 let flags =
                   FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
                     (FStar_List.map
                        (fun uu___5_4997  ->
                           match uu___5_4997 with
                           | FStar_Syntax_Syntax.DECREASES t ->
                               let uu____5001 =
                                 inline_closure_env cfg env [] t  in
                               FStar_Syntax_Syntax.DECREASES uu____5001
                           | f -> f))
                    in
                 let uu____5005 =
                   let uu___599_5006 = c1  in
                   let uu____5007 =
                     FStar_List.map (norm_universe cfg env)
                       c1.FStar_Syntax_Syntax.comp_univs
                      in
                   {
                     FStar_Syntax_Syntax.comp_univs = uu____5007;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___599_5006.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ = rt;
                     FStar_Syntax_Syntax.effect_args = args;
                     FStar_Syntax_Syntax.flags = flags
                   }  in
                 FStar_Syntax_Syntax.mk_Comp uu____5005)

and (filter_out_lcomp_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_All.pipe_right flags
      (FStar_List.filter
         (fun uu___6_5017  ->
            match uu___6_5017 with
            | FStar_Syntax_Syntax.DECREASES uu____5019 -> false
            | uu____5023 -> true))

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
                   (fun uu___7_5042  ->
                      match uu___7_5042 with
                      | FStar_Syntax_Syntax.DECREASES uu____5044 -> false
                      | uu____5048 -> true))
               in
            let rc1 =
              let uu___616_5051 = rc  in
              let uu____5052 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (inline_closure_env cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___616_5051.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____5052;
                FStar_Syntax_Syntax.residual_flags = flags
              }  in
            FStar_Pervasives_Native.Some rc1
        | uu____5061 -> lopt

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
    let uu____5109 = FStar_ST.op_Bang unembed_binder_knot  in
    match uu____5109 with
    | FStar_Pervasives_Native.Some e ->
        let uu____5148 = FStar_Syntax_Embeddings.unembed e t  in
        uu____5148 true FStar_Syntax_Embeddings.id_norm_cb
    | FStar_Pervasives_Native.None  ->
        (FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos
           (FStar_Errors.Warning_UnembedBinderKnot,
             "unembed_binder_knot is unset!");
         FStar_Pervasives_Native.None)
  
let mk_psc_subst :
  'Auu____5168 .
    FStar_TypeChecker_Cfg.cfg ->
      ((FStar_Syntax_Syntax.bv * 'Auu____5168) FStar_Pervasives_Native.option
        * closure) Prims.list -> FStar_Syntax_Syntax.subst_elt Prims.list
  =
  fun cfg  ->
    fun env  ->
      FStar_List.fold_right
        (fun uu____5230  ->
           fun subst1  ->
             match uu____5230 with
             | (binder_opt,closure) ->
                 (match (binder_opt, closure) with
                  | (FStar_Pervasives_Native.Some b,Clos
                     (env1,term,uu____5271,uu____5272)) ->
                      let uu____5333 = b  in
                      (match uu____5333 with
                       | (bv,uu____5341) ->
                           let uu____5342 =
                             let uu____5344 =
                               FStar_Syntax_Util.is_constructed_typ
                                 bv.FStar_Syntax_Syntax.sort
                                 FStar_Parser_Const.binder_lid
                                in
                             Prims.op_Negation uu____5344  in
                           if uu____5342
                           then subst1
                           else
                             (let term1 = closure_as_term cfg env1 term  in
                              let uu____5352 = unembed_binder term1  in
                              match uu____5352 with
                              | FStar_Pervasives_Native.None  -> subst1
                              | FStar_Pervasives_Native.Some x ->
                                  let b1 =
                                    let uu____5359 =
                                      let uu___651_5360 = bv  in
                                      let uu____5361 =
                                        FStar_Syntax_Subst.subst subst1
                                          (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort
                                         in
                                      {
                                        FStar_Syntax_Syntax.ppname =
                                          (uu___651_5360.FStar_Syntax_Syntax.ppname);
                                        FStar_Syntax_Syntax.index =
                                          (uu___651_5360.FStar_Syntax_Syntax.index);
                                        FStar_Syntax_Syntax.sort = uu____5361
                                      }  in
                                    FStar_Syntax_Syntax.freshen_bv uu____5359
                                     in
                                  let b_for_x =
                                    let uu____5367 =
                                      let uu____5374 =
                                        FStar_Syntax_Syntax.bv_to_name b1  in
                                      ((FStar_Pervasives_Native.fst x),
                                        uu____5374)
                                       in
                                    FStar_Syntax_Syntax.NT uu____5367  in
                                  let subst2 =
                                    FStar_List.filter
                                      (fun uu___8_5390  ->
                                         match uu___8_5390 with
                                         | FStar_Syntax_Syntax.NT
                                             (uu____5392,{
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_name
                                                             b';
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5394;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5395;_})
                                             ->
                                             let uu____5400 =
                                               FStar_Ident.ident_equals
                                                 b1.FStar_Syntax_Syntax.ppname
                                                 b'.FStar_Syntax_Syntax.ppname
                                                in
                                             Prims.op_Negation uu____5400
                                         | uu____5402 -> true) subst1
                                     in
                                  b_for_x :: subst2))
                  | uu____5404 -> subst1)) env []
  
let reduce_primops :
  'Auu____5426 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5426)
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
            (let uu____5478 = FStar_Syntax_Util.head_and_args tm  in
             match uu____5478 with
             | (head1,args) ->
                 let uu____5523 =
                   let uu____5524 = FStar_Syntax_Util.un_uinst head1  in
                   uu____5524.FStar_Syntax_Syntax.n  in
                 (match uu____5523 with
                  | FStar_Syntax_Syntax.Tm_fvar fv ->
                      let uu____5530 =
                        FStar_TypeChecker_Cfg.find_prim_step cfg fv  in
                      (match uu____5530 with
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
                                (fun uu____5553  ->
                                   let uu____5554 =
                                     FStar_Syntax_Print.lid_to_string
                                       prim_step.FStar_TypeChecker_Cfg.name
                                      in
                                   let uu____5556 =
                                     FStar_Util.string_of_int l  in
                                   let uu____5558 =
                                     FStar_Util.string_of_int
                                       prim_step.FStar_TypeChecker_Cfg.arity
                                      in
                                   FStar_Util.print3
                                     "primop: found partially applied %s (%s/%s args)\n"
                                     uu____5554 uu____5556 uu____5558);
                              tm)
                           else
                             (let uu____5563 =
                                if l = prim_step.FStar_TypeChecker_Cfg.arity
                                then (args, [])
                                else
                                  FStar_List.splitAt
                                    prim_step.FStar_TypeChecker_Cfg.arity
                                    args
                                 in
                              match uu____5563 with
                              | (args_1,args_2) ->
                                  (FStar_TypeChecker_Cfg.log_primops cfg
                                     (fun uu____5649  ->
                                        let uu____5650 =
                                          FStar_Syntax_Print.term_to_string
                                            tm
                                           in
                                        FStar_Util.print1
                                          "primop: trying to reduce <%s>\n"
                                          uu____5650);
                                   (let psc =
                                      {
                                        FStar_TypeChecker_Cfg.psc_range =
                                          (head1.FStar_Syntax_Syntax.pos);
                                        FStar_TypeChecker_Cfg.psc_subst =
                                          (fun uu____5655  ->
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
                                           (fun uu____5669  ->
                                              let uu____5670 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              FStar_Util.print1
                                                "primop: <%s> did not reduce\n"
                                                uu____5670);
                                         tm)
                                    | FStar_Pervasives_Native.Some reduced ->
                                        (FStar_TypeChecker_Cfg.log_primops
                                           cfg
                                           (fun uu____5678  ->
                                              let uu____5679 =
                                                FStar_Syntax_Print.term_to_string
                                                  tm
                                                 in
                                              let uu____5681 =
                                                FStar_Syntax_Print.term_to_string
                                                  reduced
                                                 in
                                              FStar_Util.print2
                                                "primop: <%s> reduced to <%s>\n"
                                                uu____5679 uu____5681);
                                         FStar_Syntax_Util.mk_app reduced
                                           args_2))))
                       | FStar_Pervasives_Native.Some uu____5684 ->
                           (FStar_TypeChecker_Cfg.log_primops cfg
                              (fun uu____5688  ->
                                 let uu____5689 =
                                   FStar_Syntax_Print.term_to_string tm  in
                                 FStar_Util.print1
                                   "primop: not reducing <%s> since we're doing strong reduction\n"
                                   uu____5689);
                            tm)
                       | FStar_Pervasives_Native.None  -> tm)
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5695  ->
                            let uu____5696 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5696);
                       (match args with
                        | (a1,uu____5702)::[] ->
                            FStar_TypeChecker_Cfg.embed_simple
                              FStar_Syntax_Embeddings.e_range
                              a1.FStar_Syntax_Syntax.pos
                              tm.FStar_Syntax_Syntax.pos
                        | uu____5727 -> tm))
                  | FStar_Syntax_Syntax.Tm_constant
                      (FStar_Const.Const_set_range_of ) when
                      Prims.op_Negation cfg.FStar_TypeChecker_Cfg.strong ->
                      (FStar_TypeChecker_Cfg.log_primops cfg
                         (fun uu____5741  ->
                            let uu____5742 =
                              FStar_Syntax_Print.term_to_string tm  in
                            FStar_Util.print1 "primop: reducing <%s>\n"
                              uu____5742);
                       (match args with
                        | (t,uu____5748)::(r,uu____5750)::[] ->
                            let uu____5791 =
                              FStar_TypeChecker_Cfg.try_unembed_simple
                                FStar_Syntax_Embeddings.e_range r
                               in
                            (match uu____5791 with
                             | FStar_Pervasives_Native.Some rng ->
                                 FStar_Syntax_Subst.set_use_range rng t
                             | FStar_Pervasives_Native.None  -> tm)
                        | uu____5797 -> tm))
                  | uu____5808 -> tm))
  
let reduce_equality :
  'Auu____5819 .
    FStar_Syntax_Embeddings.norm_cb ->
      FStar_TypeChecker_Cfg.cfg ->
        ((FStar_Syntax_Syntax.bv * 'Auu____5819)
          FStar_Pervasives_Native.option * closure) Prims.list ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun norm_cb  ->
    fun cfg  ->
      fun tm  ->
        reduce_primops norm_cb
          (let uu___739_5868 = cfg  in
           {
             FStar_TypeChecker_Cfg.steps =
               (let uu___741_5871 = FStar_TypeChecker_Cfg.default_steps  in
                {
                  FStar_TypeChecker_Cfg.beta =
                    (uu___741_5871.FStar_TypeChecker_Cfg.beta);
                  FStar_TypeChecker_Cfg.iota =
                    (uu___741_5871.FStar_TypeChecker_Cfg.iota);
                  FStar_TypeChecker_Cfg.zeta =
                    (uu___741_5871.FStar_TypeChecker_Cfg.zeta);
                  FStar_TypeChecker_Cfg.weak =
                    (uu___741_5871.FStar_TypeChecker_Cfg.weak);
                  FStar_TypeChecker_Cfg.hnf =
                    (uu___741_5871.FStar_TypeChecker_Cfg.hnf);
                  FStar_TypeChecker_Cfg.primops = true;
                  FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                    (uu___741_5871.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                  FStar_TypeChecker_Cfg.unfold_until =
                    (uu___741_5871.FStar_TypeChecker_Cfg.unfold_until);
                  FStar_TypeChecker_Cfg.unfold_only =
                    (uu___741_5871.FStar_TypeChecker_Cfg.unfold_only);
                  FStar_TypeChecker_Cfg.unfold_fully =
                    (uu___741_5871.FStar_TypeChecker_Cfg.unfold_fully);
                  FStar_TypeChecker_Cfg.unfold_attr =
                    (uu___741_5871.FStar_TypeChecker_Cfg.unfold_attr);
                  FStar_TypeChecker_Cfg.unfold_tac =
                    (uu___741_5871.FStar_TypeChecker_Cfg.unfold_tac);
                  FStar_TypeChecker_Cfg.pure_subterms_within_computations =
                    (uu___741_5871.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                  FStar_TypeChecker_Cfg.simplify =
                    (uu___741_5871.FStar_TypeChecker_Cfg.simplify);
                  FStar_TypeChecker_Cfg.erase_universes =
                    (uu___741_5871.FStar_TypeChecker_Cfg.erase_universes);
                  FStar_TypeChecker_Cfg.allow_unbound_universes =
                    (uu___741_5871.FStar_TypeChecker_Cfg.allow_unbound_universes);
                  FStar_TypeChecker_Cfg.reify_ =
                    (uu___741_5871.FStar_TypeChecker_Cfg.reify_);
                  FStar_TypeChecker_Cfg.compress_uvars =
                    (uu___741_5871.FStar_TypeChecker_Cfg.compress_uvars);
                  FStar_TypeChecker_Cfg.no_full_norm =
                    (uu___741_5871.FStar_TypeChecker_Cfg.no_full_norm);
                  FStar_TypeChecker_Cfg.check_no_uvars =
                    (uu___741_5871.FStar_TypeChecker_Cfg.check_no_uvars);
                  FStar_TypeChecker_Cfg.unmeta =
                    (uu___741_5871.FStar_TypeChecker_Cfg.unmeta);
                  FStar_TypeChecker_Cfg.unascribe =
                    (uu___741_5871.FStar_TypeChecker_Cfg.unascribe);
                  FStar_TypeChecker_Cfg.in_full_norm_request =
                    (uu___741_5871.FStar_TypeChecker_Cfg.in_full_norm_request);
                  FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                    (uu___741_5871.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                  FStar_TypeChecker_Cfg.nbe_step =
                    (uu___741_5871.FStar_TypeChecker_Cfg.nbe_step);
                  FStar_TypeChecker_Cfg.for_extraction =
                    (uu___741_5871.FStar_TypeChecker_Cfg.for_extraction)
                });
             FStar_TypeChecker_Cfg.tcenv =
               (uu___739_5868.FStar_TypeChecker_Cfg.tcenv);
             FStar_TypeChecker_Cfg.debug =
               (uu___739_5868.FStar_TypeChecker_Cfg.debug);
             FStar_TypeChecker_Cfg.delta_level =
               (uu___739_5868.FStar_TypeChecker_Cfg.delta_level);
             FStar_TypeChecker_Cfg.primitive_steps =
               FStar_TypeChecker_Cfg.equality_ops;
             FStar_TypeChecker_Cfg.strong =
               (uu___739_5868.FStar_TypeChecker_Cfg.strong);
             FStar_TypeChecker_Cfg.memoize_lazy =
               (uu___739_5868.FStar_TypeChecker_Cfg.memoize_lazy);
             FStar_TypeChecker_Cfg.normalize_pure_lets =
               (uu___739_5868.FStar_TypeChecker_Cfg.normalize_pure_lets);
             FStar_TypeChecker_Cfg.reifying =
               (uu___739_5868.FStar_TypeChecker_Cfg.reifying)
           }) tm
  
type norm_request_t =
  | Norm_request_none 
  | Norm_request_ready 
  | Norm_request_requires_rejig 
let (uu___is_Norm_request_none : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_none  -> true | uu____5882 -> false
  
let (uu___is_Norm_request_ready : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Norm_request_ready  -> true | uu____5893 -> false
  
let (uu___is_Norm_request_requires_rejig : norm_request_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Norm_request_requires_rejig  -> true
    | uu____5904 -> false
  
let (is_norm_request :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.args -> norm_request_t) =
  fun hd1  ->
    fun args  ->
      let aux min_args =
        let uu____5925 = FStar_All.pipe_right args FStar_List.length  in
        FStar_All.pipe_right uu____5925
          (fun n1  ->
             if n1 < min_args
             then Norm_request_none
             else
               if n1 = min_args
               then Norm_request_ready
               else Norm_request_requires_rejig)
         in
      let uu____5957 =
        let uu____5958 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5958.FStar_Syntax_Syntax.n  in
      match uu____5957 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          -> aux (Prims.parse_int "2")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          aux (Prims.parse_int "1")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          aux (Prims.parse_int "3")
      | uu____5967 -> Norm_request_none
  
let (should_consider_norm_requests : FStar_TypeChecker_Cfg.cfg -> Prims.bool)
  =
  fun cfg  ->
    (Prims.op_Negation
       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm)
      &&
      (let uu____5976 =
         FStar_Ident.lid_equals
           (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.curmodule
           FStar_Parser_Const.prims_lid
          in
       Prims.op_Negation uu____5976)
  
let (rejig_norm_request :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.term)
  =
  fun hd1  ->
    fun args  ->
      let uu____5989 =
        let uu____5990 = FStar_Syntax_Util.un_uinst hd1  in
        uu____5990.FStar_Syntax_Syntax.n  in
      match uu____5989 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize_term
          ->
          (match args with
           | t1::t2::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____6048 = FStar_Syntax_Util.mk_app hd1 [t1; t2]  in
               FStar_Syntax_Util.mk_app uu____6048 rest
           | uu____6075 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize_term")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.normalize ->
          (match args with
           | t::rest when (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____6115 = FStar_Syntax_Util.mk_app hd1 [t]  in
               FStar_Syntax_Util.mk_app uu____6115 rest
           | uu____6134 ->
               failwith
                 "Impossible! invalid rejig_norm_request for normalize")
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.norm ->
          (match args with
           | t1::t2::t3::rest when
               (FStar_List.length rest) > (Prims.parse_int "0") ->
               let uu____6208 = FStar_Syntax_Util.mk_app hd1 [t1; t2; t3]  in
               FStar_Syntax_Util.mk_app uu____6208 rest
           | uu____6243 ->
               failwith "Impossible! invalid rejig_norm_request for norm")
      | uu____6245 ->
          let uu____6246 =
            let uu____6248 = FStar_Syntax_Print.term_to_string hd1  in
            FStar_String.op_Hat
              "Impossible! invalid rejig_norm_request for: %s" uu____6248
             in
          failwith uu____6246
  
let (is_nbe_request : FStar_TypeChecker_Env.step Prims.list -> Prims.bool) =
  fun s  ->
    FStar_Util.for_some
      (FStar_TypeChecker_Env.eq_step FStar_TypeChecker_Env.NBE) s
  
let (tr_norm_step :
  FStar_Syntax_Embeddings.norm_step -> FStar_TypeChecker_Env.step Prims.list)
  =
  fun uu___9_6269  ->
    match uu___9_6269 with
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
        let uu____6276 =
          let uu____6279 =
            let uu____6280 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldOnly uu____6280  in
          [uu____6279]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6276
    | FStar_Syntax_Embeddings.UnfoldFully names1 ->
        let uu____6288 =
          let uu____6291 =
            let uu____6292 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldFully uu____6292  in
          [uu____6291]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6288
    | FStar_Syntax_Embeddings.UnfoldAttr names1 ->
        let uu____6300 =
          let uu____6303 =
            let uu____6304 = FStar_List.map FStar_Ident.lid_of_str names1  in
            FStar_TypeChecker_Env.UnfoldAttr uu____6304  in
          [uu____6303]  in
        (FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant)
          :: uu____6300
    | FStar_Syntax_Embeddings.NBE  -> [FStar_TypeChecker_Env.NBE]
  
let (tr_norm_steps :
  FStar_Syntax_Embeddings.norm_step Prims.list ->
    FStar_TypeChecker_Env.step Prims.list)
  = fun s  -> FStar_List.concatMap tr_norm_step s 
let get_norm_request :
  'Auu____6329 .
    FStar_TypeChecker_Cfg.cfg ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        (FStar_Syntax_Syntax.term * 'Auu____6329) Prims.list ->
          (FStar_TypeChecker_Env.step Prims.list * FStar_Syntax_Syntax.term)
            FStar_Pervasives_Native.option
  =
  fun cfg  ->
    fun full_norm  ->
      fun args  ->
        let parse_steps s =
          let uu____6380 =
            let uu____6385 =
              FStar_Syntax_Embeddings.e_list
                FStar_Syntax_Embeddings.e_norm_step
               in
            FStar_TypeChecker_Cfg.try_unembed_simple uu____6385 s  in
          match uu____6380 with
          | FStar_Pervasives_Native.Some steps ->
              let uu____6401 = tr_norm_steps steps  in
              FStar_Pervasives_Native.Some uu____6401
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
        | uu____6436::(tm,uu____6438)::[] ->
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
        | (tm,uu____6467)::[] ->
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
        | (steps,uu____6488)::uu____6489::(tm,uu____6491)::[] ->
            let add_exclude s z =
              let uu____6529 =
                FStar_Util.for_some (FStar_TypeChecker_Env.eq_step z) s  in
              if uu____6529
              then s
              else (FStar_TypeChecker_Env.Exclude z) :: s  in
            let uu____6536 =
              let uu____6541 = full_norm steps  in parse_steps uu____6541  in
            (match uu____6536 with
             | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
             | FStar_Pervasives_Native.Some s ->
                 let s1 = FStar_TypeChecker_Env.Beta :: s  in
                 let s2 = add_exclude s1 FStar_TypeChecker_Env.Zeta  in
                 let s3 = add_exclude s2 FStar_TypeChecker_Env.Iota  in
                 FStar_Pervasives_Native.Some
                   ((FStar_List.append inherited_steps s3), tm))
        | uu____6580 -> FStar_Pervasives_Native.None
  
let (nbe_eval :
  FStar_TypeChecker_Cfg.cfg ->
    FStar_TypeChecker_Env.steps ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun s  ->
      fun tm  ->
        let delta_level =
          let uu____6612 =
            FStar_All.pipe_right s
              (FStar_Util.for_some
                 (fun uu___10_6619  ->
                    match uu___10_6619 with
                    | FStar_TypeChecker_Env.UnfoldUntil uu____6621 -> true
                    | FStar_TypeChecker_Env.UnfoldOnly uu____6623 -> true
                    | FStar_TypeChecker_Env.UnfoldFully uu____6627 -> true
                    | uu____6631 -> false))
             in
          if uu____6612
          then
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
          else [FStar_TypeChecker_Env.NoDelta]  in
        FStar_TypeChecker_Cfg.log_nbe cfg
          (fun uu____6641  ->
             let uu____6642 = FStar_Syntax_Print.term_to_string tm  in
             FStar_Util.print1 "Invoking NBE with  %s\n" uu____6642);
        (let tm_norm =
           let uu____6646 =
             let uu____6661 = FStar_TypeChecker_Cfg.cfg_env cfg  in
             uu____6661.FStar_TypeChecker_Env.nbe  in
           uu____6646 s cfg.FStar_TypeChecker_Cfg.tcenv tm  in
         FStar_TypeChecker_Cfg.log_nbe cfg
           (fun uu____6665  ->
              let uu____6666 = FStar_Syntax_Print.term_to_string tm_norm  in
              FStar_Util.print1 "Result of NBE is  %s\n" uu____6666);
         tm_norm)
  
let (is_reify_head : stack_elt Prims.list -> Prims.bool) =
  fun uu___11_6677  ->
    match uu___11_6677 with
    | (App
        (uu____6681,{
                      FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                        (FStar_Const.Const_reify );
                      FStar_Syntax_Syntax.pos = uu____6682;
                      FStar_Syntax_Syntax.vars = uu____6683;_},uu____6684,uu____6685))::uu____6686
        -> true
    | uu____6692 -> false
  
let firstn :
  'Auu____6703 .
    Prims.int ->
      'Auu____6703 Prims.list ->
        ('Auu____6703 Prims.list * 'Auu____6703 Prims.list)
  =
  fun k  ->
    fun l  ->
      if (FStar_List.length l) < k then (l, []) else FStar_Util.first_N k l
  
let (should_reify :
  FStar_TypeChecker_Cfg.cfg -> stack_elt Prims.list -> Prims.bool) =
  fun cfg  ->
    fun stack  ->
      let rec drop_irrel uu___12_6760 =
        match uu___12_6760 with
        | (MemoLazy uu____6765)::s -> drop_irrel s
        | (UnivArgs uu____6775)::s -> drop_irrel s
        | s -> s  in
      let uu____6788 = drop_irrel stack  in
      match uu____6788 with
      | (App
          (uu____6792,{
                        FStar_Syntax_Syntax.n =
                          FStar_Syntax_Syntax.Tm_constant
                          (FStar_Const.Const_reify );
                        FStar_Syntax_Syntax.pos = uu____6793;
                        FStar_Syntax_Syntax.vars = uu____6794;_},uu____6795,uu____6796))::uu____6797
          -> (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.reify_
      | uu____6802 -> false
  
let rec (maybe_weakly_reduced :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun tm  ->
    let aux_comp c =
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.GTotal (t,uu____6831) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Total (t,uu____6841) -> maybe_weakly_reduced t
      | FStar_Syntax_Syntax.Comp ct ->
          (maybe_weakly_reduced ct.FStar_Syntax_Syntax.result_typ) ||
            (FStar_Util.for_some
               (fun uu____6862  ->
                  match uu____6862 with
                  | (a,uu____6873) -> maybe_weakly_reduced a)
               ct.FStar_Syntax_Syntax.effect_args)
       in
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6884 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name uu____6909 -> false
    | FStar_Syntax_Syntax.Tm_uvar uu____6911 -> false
    | FStar_Syntax_Syntax.Tm_type uu____6925 -> false
    | FStar_Syntax_Syntax.Tm_bvar uu____6927 -> false
    | FStar_Syntax_Syntax.Tm_fvar uu____6929 -> false
    | FStar_Syntax_Syntax.Tm_constant uu____6931 -> false
    | FStar_Syntax_Syntax.Tm_lazy uu____6933 -> false
    | FStar_Syntax_Syntax.Tm_unknown  -> false
    | FStar_Syntax_Syntax.Tm_uinst uu____6936 -> false
    | FStar_Syntax_Syntax.Tm_quoted uu____6944 -> false
    | FStar_Syntax_Syntax.Tm_let uu____6952 -> true
    | FStar_Syntax_Syntax.Tm_abs uu____6967 -> true
    | FStar_Syntax_Syntax.Tm_arrow uu____6987 -> true
    | FStar_Syntax_Syntax.Tm_refine uu____7003 -> true
    | FStar_Syntax_Syntax.Tm_match uu____7011 -> true
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        (maybe_weakly_reduced t1) ||
          (FStar_All.pipe_right args
             (FStar_Util.for_some
                (fun uu____7083  ->
                   match uu____7083 with
                   | (a,uu____7094) -> maybe_weakly_reduced a)))
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____7105) ->
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
            | FStar_Syntax_Syntax.Meta_pattern (uu____7205,args,uu____7207)
                ->
                FStar_Util.for_some
                  (FStar_Util.for_some
                     (fun uu____7263  ->
                        match uu____7263 with
                        | (a,uu____7274) -> maybe_weakly_reduced a)) args
            | FStar_Syntax_Syntax.Meta_monadic_lift
                (uu____7283,uu____7284,t') -> maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_monadic (uu____7290,t') ->
                maybe_weakly_reduced t'
            | FStar_Syntax_Syntax.Meta_labeled uu____7296 -> false
            | FStar_Syntax_Syntax.Meta_desugared uu____7306 -> false
            | FStar_Syntax_Syntax.Meta_named uu____7308 -> false))
  
type should_unfold_res =
  | Should_unfold_no 
  | Should_unfold_yes 
  | Should_unfold_fully 
  | Should_unfold_reify 
let (uu___is_Should_unfold_no : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_no  -> true | uu____7319 -> false
  
let (uu___is_Should_unfold_yes : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_yes  -> true | uu____7330 -> false
  
let (uu___is_Should_unfold_fully : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_fully  -> true | uu____7341 -> false
  
let (uu___is_Should_unfold_reify : should_unfold_res -> Prims.bool) =
  fun projectee  ->
    match projectee with | Should_unfold_reify  -> true | uu____7352 -> false
  
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
            let uu____7385 = FStar_TypeChecker_Env.attrs_of_qninfo qninfo  in
            match uu____7385 with
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
              (fun uu____7584  ->
                 fun uu____7585  ->
                   match (uu____7584, uu____7585) with
                   | ((a,b,c),(x,y,z)) -> ((a || x), (b || y), (c || z))) l
              (false, false, false)
             in
          let string_of_res uu____7691 =
            match uu____7691 with
            | (x,y,z) ->
                let uu____7711 = FStar_Util.string_of_bool x  in
                let uu____7713 = FStar_Util.string_of_bool y  in
                let uu____7715 = FStar_Util.string_of_bool z  in
                FStar_Util.format3 "(%s,%s,%s)" uu____7711 uu____7713
                  uu____7715
             in
          let res =
            if FStar_TypeChecker_Env.qninfo_is_action qninfo
            then
              let b = should_reify1 cfg  in
              (FStar_TypeChecker_Cfg.log_unfolding cfg
                 (fun uu____7743  ->
                    let uu____7744 = FStar_Syntax_Print.fv_to_string fv  in
                    let uu____7746 = FStar_Util.string_of_bool b  in
                    FStar_Util.print2
                      "should_unfold: For DM4F action %s, should_reify = %s\n"
                      uu____7744 uu____7746);
               if b then reif else no)
            else
              if
                (let uu____7761 = FStar_TypeChecker_Cfg.find_prim_step cfg fv
                    in
                 FStar_Option.isSome uu____7761)
              then
                (FStar_TypeChecker_Cfg.log_unfolding cfg
                   (fun uu____7766  ->
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
                          ((is_rec,uu____7801),uu____7802);
                        FStar_Syntax_Syntax.sigrng = uu____7803;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7805;
                        FStar_Syntax_Syntax.sigattrs = uu____7806;_},uu____7807),uu____7808),uu____7809,uu____7810,uu____7811)
                     when
                     FStar_List.contains FStar_Syntax_Syntax.HasMaskedEffect
                       qs
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7918  ->
                           FStar_Util.print_string
                             " >> HasMaskedEffect, not unfolding\n");
                      no)
                 | (uu____7920,uu____7921,uu____7922,uu____7923) when
                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_tac
                       &&
                       (FStar_Util.for_some
                          (FStar_Syntax_Util.attr_eq
                             FStar_Syntax_Util.tac_opaque_attr) attrs)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____7990  ->
                           FStar_Util.print_string
                             " >> tac_opaque, not unfolding\n");
                      no)
                 | (FStar_Pervasives_Native.Some
                    (FStar_Util.Inr
                     ({
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let
                          ((is_rec,uu____7993),uu____7994);
                        FStar_Syntax_Syntax.sigrng = uu____7995;
                        FStar_Syntax_Syntax.sigquals = qs;
                        FStar_Syntax_Syntax.sigmeta = uu____7997;
                        FStar_Syntax_Syntax.sigattrs = uu____7998;_},uu____7999),uu____8000),uu____8001,uu____8002,uu____8003)
                     when
                     is_rec &&
                       (Prims.op_Negation
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta)
                     ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8110  ->
                           FStar_Util.print_string
                             " >> It's a recursive definition but we're not doing Zeta, not unfolding\n");
                      no)
                 | (uu____8112,FStar_Pervasives_Native.Some
                    uu____8113,uu____8114,uu____8115) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8183  ->
                           let uu____8184 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8184);
                      (let uu____8187 =
                         let uu____8199 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8225 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8225
                            in
                         let uu____8237 =
                           let uu____8249 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8275 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8275
                              in
                           let uu____8291 =
                             let uu____8303 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8329 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8329
                                in
                             [uu____8303]  in
                           uu____8249 :: uu____8291  in
                         uu____8199 :: uu____8237  in
                       comb_or uu____8187))
                 | (uu____8377,uu____8378,FStar_Pervasives_Native.Some
                    uu____8379,uu____8380) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8448  ->
                           let uu____8449 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8449);
                      (let uu____8452 =
                         let uu____8464 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8490 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8490
                            in
                         let uu____8502 =
                           let uu____8514 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8540 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8540
                              in
                           let uu____8556 =
                             let uu____8568 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8594 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8594
                                in
                             [uu____8568]  in
                           uu____8514 :: uu____8556  in
                         uu____8464 :: uu____8502  in
                       comb_or uu____8452))
                 | (uu____8642,uu____8643,uu____8644,FStar_Pervasives_Native.Some
                    uu____8645) ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8713  ->
                           let uu____8714 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           FStar_Util.print1
                             "should_unfold: Reached a %s with selective unfolding\n"
                             uu____8714);
                      (let uu____8717 =
                         let uu____8729 =
                           match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_only
                           with
                           | FStar_Pervasives_Native.None  -> no
                           | FStar_Pervasives_Native.Some lids ->
                               let uu____8755 =
                                 FStar_Util.for_some
                                   (FStar_Syntax_Syntax.fv_eq_lid fv) lids
                                  in
                               FStar_All.pipe_left yesno uu____8755
                            in
                         let uu____8767 =
                           let uu____8779 =
                             match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_attr
                             with
                             | FStar_Pervasives_Native.None  -> no
                             | FStar_Pervasives_Native.Some lids ->
                                 let uu____8805 =
                                   FStar_Util.for_some
                                     (fun at  ->
                                        FStar_Util.for_some
                                          (fun lid  ->
                                             FStar_Syntax_Util.is_fvar lid at)
                                          lids) attrs
                                    in
                                 FStar_All.pipe_left yesno uu____8805
                              in
                           let uu____8821 =
                             let uu____8833 =
                               match (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unfold_fully
                               with
                               | FStar_Pervasives_Native.None  -> no
                               | FStar_Pervasives_Native.Some lids ->
                                   let uu____8859 =
                                     FStar_Util.for_some
                                       (FStar_Syntax_Syntax.fv_eq_lid fv)
                                       lids
                                      in
                                   FStar_All.pipe_left fullyno uu____8859
                                in
                             [uu____8833]  in
                           uu____8779 :: uu____8821  in
                         uu____8729 :: uu____8767  in
                       comb_or uu____8717))
                 | uu____8907 ->
                     (FStar_TypeChecker_Cfg.log_unfolding cfg
                        (fun uu____8953  ->
                           let uu____8954 =
                             FStar_Syntax_Print.fv_to_string fv  in
                           let uu____8956 =
                             FStar_Syntax_Print.delta_depth_to_string
                               fv.FStar_Syntax_Syntax.fv_delta
                              in
                           let uu____8958 =
                             FStar_Common.string_of_list
                               FStar_TypeChecker_Env.string_of_delta_level
                               cfg.FStar_TypeChecker_Cfg.delta_level
                              in
                           FStar_Util.print3
                             "should_unfold: Reached a %s with delta_depth = %s\n >> Our delta_level is %s\n"
                             uu____8954 uu____8956 uu____8958);
                      (let uu____8961 =
                         FStar_All.pipe_right
                           cfg.FStar_TypeChecker_Cfg.delta_level
                           (FStar_Util.for_some
                              (fun uu___13_8967  ->
                                 match uu___13_8967 with
                                 | FStar_TypeChecker_Env.NoDelta  -> false
                                 | FStar_TypeChecker_Env.InliningDelta  ->
                                     true
                                 | FStar_TypeChecker_Env.Eager_unfolding_only
                                      -> true
                                 | FStar_TypeChecker_Env.Unfold l ->
                                     let uu____8973 =
                                       FStar_TypeChecker_Env.delta_depth_of_fv
                                         cfg.FStar_TypeChecker_Cfg.tcenv fv
                                        in
                                     FStar_TypeChecker_Common.delta_depth_greater_than
                                       uu____8973 l))
                          in
                       FStar_All.pipe_left yesno uu____8961)))
             in
          FStar_TypeChecker_Cfg.log_unfolding cfg
            (fun uu____8989  ->
               let uu____8990 = FStar_Syntax_Print.fv_to_string fv  in
               let uu____8992 =
                 let uu____8994 = FStar_Syntax_Syntax.range_of_fv fv  in
                 FStar_Range.string_of_range uu____8994  in
               let uu____8995 = string_of_res res  in
               FStar_Util.print3
                 "should_unfold: For %s (%s), unfolding res = %s\n"
                 uu____8990 uu____8992 uu____8995);
          (match res with
           | (false ,uu____8998,uu____8999) -> Should_unfold_no
           | (true ,false ,false ) -> Should_unfold_yes
           | (true ,true ,false ) -> Should_unfold_fully
           | (true ,false ,true ) -> Should_unfold_reify
           | uu____9024 ->
               let uu____9034 =
                 let uu____9036 = string_of_res res  in
                 FStar_Util.format1 "Unexpected unfolding result: %s"
                   uu____9036
                  in
               FStar_All.pipe_left failwith uu____9034)
  
let decide_unfolding :
  'Auu____9055 .
    FStar_TypeChecker_Cfg.cfg ->
      env ->
        stack_elt Prims.list ->
          'Auu____9055 ->
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
                    let uu___1161_9124 = cfg  in
                    {
                      FStar_TypeChecker_Cfg.steps =
                        (let uu___1163_9127 = cfg.FStar_TypeChecker_Cfg.steps
                            in
                         {
                           FStar_TypeChecker_Cfg.beta =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.beta);
                           FStar_TypeChecker_Cfg.iota =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.iota);
                           FStar_TypeChecker_Cfg.zeta =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.zeta);
                           FStar_TypeChecker_Cfg.weak =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.weak);
                           FStar_TypeChecker_Cfg.hnf =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.hnf);
                           FStar_TypeChecker_Cfg.primops =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.primops);
                           FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
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
                             (uu___1163_9127.FStar_TypeChecker_Cfg.unfold_tac);
                           FStar_TypeChecker_Cfg.pure_subterms_within_computations
                             =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                           FStar_TypeChecker_Cfg.simplify =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.simplify);
                           FStar_TypeChecker_Cfg.erase_universes =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.erase_universes);
                           FStar_TypeChecker_Cfg.allow_unbound_universes =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.allow_unbound_universes);
                           FStar_TypeChecker_Cfg.reify_ =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.reify_);
                           FStar_TypeChecker_Cfg.compress_uvars =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.compress_uvars);
                           FStar_TypeChecker_Cfg.no_full_norm =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.no_full_norm);
                           FStar_TypeChecker_Cfg.check_no_uvars =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.check_no_uvars);
                           FStar_TypeChecker_Cfg.unmeta =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.unmeta);
                           FStar_TypeChecker_Cfg.unascribe =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.unascribe);
                           FStar_TypeChecker_Cfg.in_full_norm_request =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.in_full_norm_request);
                           FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                           FStar_TypeChecker_Cfg.nbe_step =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.nbe_step);
                           FStar_TypeChecker_Cfg.for_extraction =
                             (uu___1163_9127.FStar_TypeChecker_Cfg.for_extraction)
                         });
                      FStar_TypeChecker_Cfg.tcenv =
                        (uu___1161_9124.FStar_TypeChecker_Cfg.tcenv);
                      FStar_TypeChecker_Cfg.debug =
                        (uu___1161_9124.FStar_TypeChecker_Cfg.debug);
                      FStar_TypeChecker_Cfg.delta_level =
                        (uu___1161_9124.FStar_TypeChecker_Cfg.delta_level);
                      FStar_TypeChecker_Cfg.primitive_steps =
                        (uu___1161_9124.FStar_TypeChecker_Cfg.primitive_steps);
                      FStar_TypeChecker_Cfg.strong =
                        (uu___1161_9124.FStar_TypeChecker_Cfg.strong);
                      FStar_TypeChecker_Cfg.memoize_lazy =
                        (uu___1161_9124.FStar_TypeChecker_Cfg.memoize_lazy);
                      FStar_TypeChecker_Cfg.normalize_pure_lets =
                        (uu___1161_9124.FStar_TypeChecker_Cfg.normalize_pure_lets);
                      FStar_TypeChecker_Cfg.reifying =
                        (uu___1161_9124.FStar_TypeChecker_Cfg.reifying)
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
                        let uu____9189 = push1 e t  in (UnivArgs (us, r)) ::
                          uu____9189
                    | h::t -> e :: h :: t  in
                  let ref =
                    let uu____9201 =
                      let uu____9208 =
                        let uu____9209 =
                          let uu____9210 = FStar_Syntax_Syntax.lid_of_fv fv
                             in
                          FStar_Const.Const_reflect uu____9210  in
                        FStar_Syntax_Syntax.Tm_constant uu____9209  in
                      FStar_Syntax_Syntax.mk uu____9208  in
                    uu____9201 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  let stack1 =
                    push1
                      (App
                         (env, ref, FStar_Pervasives_Native.None,
                           FStar_Range.dummyRange)) stack
                     in
                  FStar_Pervasives_Native.Some (cfg, stack1)
  
let (is_fext_on_domain :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let fext_lid s =
      FStar_Ident.lid_of_path ["FStar"; "FunctionalExtensionality"; s]
        FStar_Range.dummyRange
       in
    let on_domain_lids =
      FStar_All.pipe_right ["on_domain"; "on_dom"; "on_domain_g"; "on_dom_g"]
        (FStar_List.map fext_lid)
       in
    let is_on_dom fv =
      FStar_All.pipe_right on_domain_lids
        (FStar_List.existsb (fun l  -> FStar_Syntax_Syntax.fv_eq_lid fv l))
       in
    let uu____9276 =
      let uu____9277 = FStar_Syntax_Subst.compress t  in
      uu____9277.FStar_Syntax_Syntax.n  in
    match uu____9276 with
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____9308 =
          let uu____9309 = FStar_Syntax_Util.un_uinst hd1  in
          uu____9309.FStar_Syntax_Syntax.n  in
        (match uu____9308 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             (is_on_dom fv) &&
               ((FStar_List.length args) = (Prims.parse_int "3"))
             ->
             let f =
               let uu____9326 =
                 let uu____9333 =
                   let uu____9344 = FStar_All.pipe_right args FStar_List.tl
                      in
                   FStar_All.pipe_right uu____9344 FStar_List.tl  in
                 FStar_All.pipe_right uu____9333 FStar_List.hd  in
               FStar_All.pipe_right uu____9326 FStar_Pervasives_Native.fst
                in
             FStar_Pervasives_Native.Some f
         | uu____9443 -> FStar_Pervasives_Native.None)
    | uu____9444 -> FStar_Pervasives_Native.None
  
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
               | FStar_Syntax_Syntax.Tm_delayed uu____9723 ->
                   let uu____9746 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "NORM delayed: %s\n" uu____9746
               | uu____9749 -> ())
            else ();
            FStar_Syntax_Subst.compress t  in
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____9759  ->
               let uu____9760 = FStar_Syntax_Print.tag_of_term t1  in
               let uu____9762 =
                 FStar_Util.string_of_bool
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.no_full_norm
                  in
               let uu____9764 = FStar_Syntax_Print.term_to_string t1  in
               let uu____9766 =
                 FStar_Util.string_of_int (FStar_List.length env)  in
               let uu____9774 =
                 let uu____9776 =
                   let uu____9779 = firstn (Prims.parse_int "4") stack  in
                   FStar_All.pipe_left FStar_Pervasives_Native.fst uu____9779
                    in
                 stack_to_string uu____9776  in
               FStar_Util.print5
                 ">>> %s (no_full_norm=%s)\nNorm %s  with with %s env elements top of the stack %s \n"
                 uu____9760 uu____9762 uu____9764 uu____9766 uu____9774);
          FStar_TypeChecker_Cfg.log_cfg cfg
            (fun uu____9807  ->
               let uu____9808 = FStar_TypeChecker_Cfg.cfg_to_string cfg  in
               FStar_Util.print1 ">>> cfg = %s\n" uu____9808);
          (match t1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_unknown  ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9814  ->
                     let uu____9815 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9815);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_constant uu____9818 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9822  ->
                     let uu____9823 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9823);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_name uu____9826 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9830  ->
                     let uu____9831 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9831);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_lazy uu____9834 ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9838  ->
                     let uu____9839 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9839);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9842;
                 FStar_Syntax_Syntax.fv_delta = uu____9843;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Data_ctor );_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9847  ->
                     let uu____9848 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9848);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar
               { FStar_Syntax_Syntax.fv_name = uu____9851;
                 FStar_Syntax_Syntax.fv_delta = uu____9852;
                 FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Record_ctor uu____9853);_}
               ->
               (FStar_TypeChecker_Cfg.log_unfolding cfg
                  (fun uu____9863  ->
                     let uu____9864 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                       uu____9864);
                rebuild cfg env stack t1)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
               let qninfo =
                 FStar_TypeChecker_Env.lookup_qname
                   cfg.FStar_TypeChecker_Cfg.tcenv lid
                  in
               let uu____9870 =
                 FStar_TypeChecker_Env.delta_depth_of_qninfo fv qninfo  in
               (match uu____9870 with
                | FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Delta_constant_at_level _9873) when
                    _9873 = (Prims.parse_int "0") ->
                    (FStar_TypeChecker_Cfg.log_unfolding cfg
                       (fun uu____9877  ->
                          let uu____9878 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 ">>> Tm_fvar case 0 for %s\n"
                            uu____9878);
                     rebuild cfg env stack t1)
                | uu____9881 ->
                    let uu____9884 =
                      decide_unfolding cfg env stack
                        t1.FStar_Syntax_Syntax.pos fv qninfo
                       in
                    (match uu____9884 with
                     | FStar_Pervasives_Native.Some (cfg1,stack1) ->
                         do_unfold_fv cfg1 env stack1 t1 qninfo fv
                     | FStar_Pervasives_Native.None  ->
                         rebuild cfg env stack t1))
           | FStar_Syntax_Syntax.Tm_quoted uu____9911 ->
               let uu____9918 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____9918
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9946 = is_norm_request hd1 args  in
                  uu____9946 = Norm_request_requires_rejig)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Rejigging norm request ... \n"
                else ();
                (let uu____9952 = rejig_norm_request hd1 args  in
                 norm cfg env stack uu____9952))
           | FStar_Syntax_Syntax.Tm_app (hd1,args) when
               (should_consider_norm_requests cfg) &&
                 (let uu____9980 = is_norm_request hd1 args  in
                  uu____9980 = Norm_request_ready)
               ->
               (if
                  (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                then FStar_Util.print_string "Potential norm request ... \n"
                else ();
                (let cfg' =
                   let uu___1271_9987 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1273_9990 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.weak);
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            false;
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_fully =
                            FStar_Pervasives_Native.None;
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1273_9990.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1271_9987.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1271_9987.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       [FStar_TypeChecker_Env.Unfold
                          FStar_Syntax_Syntax.delta_constant];
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1271_9987.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1271_9987.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1271_9987.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1271_9987.FStar_TypeChecker_Cfg.reifying)
                   }  in
                 let uu____9997 =
                   get_norm_request cfg (norm cfg' env []) args  in
                 match uu____9997 with
                 | FStar_Pervasives_Native.None  ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then FStar_Util.print_string "Norm request None ... \n"
                      else ();
                      (let stack1 =
                         FStar_All.pipe_right stack
                           (FStar_List.fold_right
                              (fun uu____10033  ->
                                 fun stack1  ->
                                   match uu____10033 with
                                   | (a,aq) ->
                                       let uu____10045 =
                                         let uu____10046 =
                                           let uu____10053 =
                                             let uu____10054 =
                                               let uu____10086 =
                                                 FStar_Util.mk_ref
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env, a, uu____10086, false)
                                                in
                                             Clos uu____10054  in
                                           (uu____10053, aq,
                                             (t1.FStar_Syntax_Syntax.pos))
                                            in
                                         Arg uu____10046  in
                                       uu____10045 :: stack1) args)
                          in
                       FStar_TypeChecker_Cfg.log cfg
                         (fun uu____10154  ->
                            let uu____10155 =
                              FStar_All.pipe_left FStar_Util.string_of_int
                                (FStar_List.length args)
                               in
                            FStar_Util.print1 "\tPushed %s arguments\n"
                              uu____10155);
                       norm cfg env stack1 hd1))
                 | FStar_Pervasives_Native.Some (s,tm) when is_nbe_request s
                     ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10182 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting NBE request on %s ... \n" uu____10182)
                      else ();
                      (let tm' = closure_as_term cfg env tm  in
                       let start = FStar_Util.now ()  in
                       let tm_norm = nbe_eval cfg s tm'  in
                       let fin = FStar_Util.now ()  in
                       if
                         (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                       then
                         (let uu____10193 =
                            let uu____10195 =
                              let uu____10197 =
                                FStar_Util.time_diff start fin  in
                              FStar_Pervasives_Native.snd uu____10197  in
                            FStar_Util.string_of_int uu____10195  in
                          let uu____10204 =
                            FStar_Syntax_Print.term_to_string tm'  in
                          let uu____10206 =
                            FStar_Syntax_Print.term_to_string tm_norm  in
                          FStar_Util.print3 "NBE'd (%s ms) %s\n\tto %s\n"
                            uu____10193 uu____10204 uu____10206)
                       else ();
                       norm cfg env stack tm_norm))
                 | FStar_Pervasives_Native.Some (s,tm) ->
                     (if
                        (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                      then
                        (let uu____10225 =
                           FStar_Syntax_Print.term_to_string tm  in
                         FStar_Util.print1
                           "Starting norm request on %s ... \n" uu____10225)
                      else ();
                      (let delta_level =
                         let uu____10233 =
                           FStar_All.pipe_right s
                             (FStar_Util.for_some
                                (fun uu___14_10240  ->
                                   match uu___14_10240 with
                                   | FStar_TypeChecker_Env.UnfoldUntil
                                       uu____10242 -> true
                                   | FStar_TypeChecker_Env.UnfoldOnly
                                       uu____10244 -> true
                                   | FStar_TypeChecker_Env.UnfoldFully
                                       uu____10248 -> true
                                   | uu____10252 -> false))
                            in
                         if uu____10233
                         then
                           [FStar_TypeChecker_Env.Unfold
                              FStar_Syntax_Syntax.delta_constant]
                         else [FStar_TypeChecker_Env.NoDelta]  in
                       let cfg'1 =
                         let uu___1314_10260 = cfg  in
                         let uu____10261 =
                           let uu___1316_10262 =
                             FStar_TypeChecker_Cfg.to_fsteps s  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.zeta);
                             FStar_TypeChecker_Cfg.weak =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.unfold_until);
                             FStar_TypeChecker_Cfg.unfold_only =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.unfold_only);
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.unfold_attr);
                             FStar_TypeChecker_Cfg.unfold_tac =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.unfold_tac);
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               true;
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___1316_10262.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         {
                           FStar_TypeChecker_Cfg.steps = uu____10261;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___1314_10260.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___1314_10260.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = delta_level;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___1314_10260.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong =
                             (uu___1314_10260.FStar_TypeChecker_Cfg.strong);
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___1314_10260.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets = true;
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___1314_10260.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let stack' =
                         let tail1 = (Cfg cfg) :: stack  in
                         if
                           (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                         then
                           let uu____10270 =
                             let uu____10271 =
                               let uu____10276 = FStar_Util.now ()  in
                               (t1, uu____10276)  in
                             Debug uu____10271  in
                           uu____10270 :: tail1
                         else tail1  in
                       norm cfg'1 env stack' tm))))
           | FStar_Syntax_Syntax.Tm_type u ->
               let u1 = norm_universe cfg env u  in
               let uu____10281 =
                 mk (FStar_Syntax_Syntax.Tm_type u1)
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____10281
           | FStar_Syntax_Syntax.Tm_uinst (t',us) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
               then norm cfg env stack t'
               else
                 (let us1 =
                    let uu____10292 =
                      let uu____10299 =
                        FStar_List.map (norm_universe cfg env) us  in
                      (uu____10299, (t1.FStar_Syntax_Syntax.pos))  in
                    UnivArgs uu____10292  in
                  let stack1 = us1 :: stack  in norm cfg env stack1 t')
           | FStar_Syntax_Syntax.Tm_bvar x ->
               let uu____10308 = lookup_bvar env x  in
               (match uu____10308 with
                | Univ uu____10309 ->
                    failwith
                      "Impossible: term variable is bound to a universe"
                | Dummy  -> failwith "Term variable not found"
                | Clos (env1,t0,r,fix) ->
                    if
                      (Prims.op_Negation fix) ||
                        (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
                    then
                      let uu____10363 = FStar_ST.op_Bang r  in
                      (match uu____10363 with
                       | FStar_Pervasives_Native.Some (env2,t') ->
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10459  ->
                                 let uu____10460 =
                                   FStar_Syntax_Print.term_to_string t1  in
                                 let uu____10462 =
                                   FStar_Syntax_Print.term_to_string t'  in
                                 FStar_Util.print2
                                   "Lazy hit: %s cached to %s\n" uu____10460
                                   uu____10462);
                            (let uu____10465 = maybe_weakly_reduced t'  in
                             if uu____10465
                             then
                               match stack with
                               | [] when
                                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                                     ||
                                     (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.compress_uvars
                                   -> rebuild cfg env2 stack t'
                               | uu____10468 -> norm cfg env2 stack t'
                             else rebuild cfg env2 stack t'))
                       | FStar_Pervasives_Native.None  ->
                           norm cfg env1 ((MemoLazy r) :: stack) t0)
                    else norm cfg env1 stack t0)
           | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
               (match stack with
                | (UnivArgs uu____10512)::uu____10513 ->
                    failwith
                      "Ill-typed term: universes cannot be applied to term abstraction"
                | (Arg (c,uu____10524,uu____10525))::stack_rest ->
                    (match c with
                     | Univ uu____10529 ->
                         norm cfg ((FStar_Pervasives_Native.None, c) :: env)
                           stack_rest t1
                     | uu____10538 ->
                         (match bs with
                          | [] -> failwith "Impossible"
                          | b::[] ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10568  ->
                                    let uu____10569 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10569);
                               norm cfg
                                 (((FStar_Pervasives_Native.Some b), c) ::
                                 env) stack_rest body)
                          | b::tl1 ->
                              (FStar_TypeChecker_Cfg.log cfg
                                 (fun uu____10605  ->
                                    let uu____10606 = closure_to_string c  in
                                    FStar_Util.print1 "\tShifted %s\n"
                                      uu____10606);
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
                       (fun uu____10654  ->
                          let uu____10655 =
                            FStar_Syntax_Print.term_to_string t1  in
                          FStar_Util.print1 "\tSet memo %s\n" uu____10655);
                     norm cfg env stack1 t1)
                | (Match uu____10658)::uu____10659 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10674 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10674 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10710  -> dummy :: env1) env)
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
                                          let uu____10754 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10754)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_10762 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_10762.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_10762.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10763 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10769  ->
                                 let uu____10770 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10770);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_10785 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_10785.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_10785.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_10785.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_10785.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_10785.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_10785.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_10785.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_10785.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Debug uu____10789)::uu____10790 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10801 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10801 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10837  -> dummy :: env1) env)
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
                                          let uu____10881 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____10881)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_10889 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_10889.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_10889.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____10890 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____10896  ->
                                 let uu____10897 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____10897);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_10912 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_10912.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_10912.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_10912.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_10912.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_10912.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_10912.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_10912.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_10912.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Meta uu____10916)::uu____10917 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____10930 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____10930 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____10966  -> dummy :: env1) env)
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
                                          let uu____11010 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11010)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_11018 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_11018.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_11018.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11019 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11025  ->
                                 let uu____11026 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11026);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_11041 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_11041.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_11041.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_11041.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_11041.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_11041.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_11041.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_11041.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_11041.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Let uu____11045)::uu____11046 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11061 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11061 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11097  -> dummy :: env1) env)
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
                                          let uu____11141 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11141)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_11149 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_11149.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_11149.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11150 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11156  ->
                                 let uu____11157 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11157);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_11172 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_11172.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_11172.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_11172.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_11172.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_11172.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_11172.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_11172.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_11172.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (App uu____11176)::uu____11177 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11192 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11192 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11228  -> dummy :: env1) env)
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
                                          let uu____11272 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11272)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_11280 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_11280.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_11280.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11281 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11287  ->
                                 let uu____11288 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11288);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_11303 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_11303.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_11303.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_11303.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_11303.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_11303.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_11303.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_11303.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_11303.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1)))
                | (Abs uu____11307)::uu____11308 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                    then
                      let t2 = closure_as_term cfg env t1  in
                      rebuild cfg env stack t2
                    else
                      (let uu____11327 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11327 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11363  -> dummy :: env1) env)
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
                                          let uu____11407 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11407)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_11415 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_11415.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_11415.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11416 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11422  ->
                                 let uu____11423 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11423);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_11438 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_11438.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_11438.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_11438.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_11438.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_11438.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_11438.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_11438.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_11438.FStar_TypeChecker_Cfg.reifying)
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
                      (let uu____11446 =
                         FStar_Syntax_Subst.open_term' bs body  in
                       match uu____11446 with
                       | (bs1,body1,opening) ->
                           let env' =
                             FStar_All.pipe_right bs1
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____11482  -> dummy :: env1) env)
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
                                          let uu____11526 =
                                            FStar_Syntax_Subst.subst opening
                                              t2
                                             in
                                          norm cfg env' [] uu____11526)
                                   else
                                     FStar_Util.map_opt
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Syntax_Subst.subst opening)
                                    in
                                 FStar_Pervasives_Native.Some
                                   (let uu___1434_11534 = rc  in
                                    {
                                      FStar_Syntax_Syntax.residual_effect =
                                        (uu___1434_11534.FStar_Syntax_Syntax.residual_effect);
                                      FStar_Syntax_Syntax.residual_typ = rct;
                                      FStar_Syntax_Syntax.residual_flags =
                                        (uu___1434_11534.FStar_Syntax_Syntax.residual_flags)
                                    })
                             | uu____11535 -> lopt  in
                           (FStar_TypeChecker_Cfg.log cfg
                              (fun uu____11541  ->
                                 let uu____11542 =
                                   FStar_All.pipe_left
                                     FStar_Util.string_of_int
                                     (FStar_List.length bs1)
                                    in
                                 FStar_Util.print1 "\tShifted %s dummies\n"
                                   uu____11542);
                            (let stack1 = (Cfg cfg) :: stack  in
                             let cfg1 =
                               let uu___1441_11557 = cfg  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1441_11557.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv =
                                   (uu___1441_11557.FStar_TypeChecker_Cfg.tcenv);
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1441_11557.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1441_11557.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1441_11557.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong = true;
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1441_11557.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1441_11557.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1441_11557.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             norm cfg1 env'
                               ((Abs
                                   (env, bs1, env', lopt1,
                                     (t1.FStar_Syntax_Syntax.pos))) ::
                               stack1) body1))))
           | FStar_Syntax_Syntax.Tm_app (head1,args) ->
               let stack1 =
                 FStar_All.pipe_right stack
                   (FStar_List.fold_right
                      (fun uu____11601  ->
                         fun stack1  ->
                           match uu____11601 with
                           | (a,aq) ->
                               let uu____11613 =
                                 let uu____11614 =
                                   let uu____11621 =
                                     let uu____11622 =
                                       let uu____11654 =
                                         FStar_Util.mk_ref
                                           FStar_Pervasives_Native.None
                                          in
                                       (env, a, uu____11654, false)  in
                                     Clos uu____11622  in
                                   (uu____11621, aq,
                                     (t1.FStar_Syntax_Syntax.pos))
                                    in
                                 Arg uu____11614  in
                               uu____11613 :: stack1) args)
                  in
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____11722  ->
                     let uu____11723 =
                       FStar_All.pipe_left FStar_Util.string_of_int
                         (FStar_List.length args)
                        in
                     FStar_Util.print1 "\tPushed %s arguments\n" uu____11723);
                norm cfg env stack1 head1)
           | FStar_Syntax_Syntax.Tm_refine (x,uu____11737) when
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
                             ((let uu___1468_11782 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1468_11782.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1468_11782.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t_x
                               }), f)) t1.FStar_Syntax_Syntax.pos
                         in
                      rebuild cfg env stack t2
                  | uu____11783 ->
                      let uu____11798 = closure_as_term cfg env t1  in
                      rebuild cfg env stack uu____11798)
               else
                 (let t_x = norm cfg env [] x.FStar_Syntax_Syntax.sort  in
                  let uu____11802 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] f
                     in
                  match uu____11802 with
                  | (closing,f1) ->
                      let f2 = norm cfg (dummy :: env) [] f1  in
                      let t2 =
                        let uu____11833 =
                          let uu____11834 =
                            let uu____11841 =
                              FStar_Syntax_Subst.close closing f2  in
                            ((let uu___1477_11847 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1477_11847.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___1477_11847.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t_x
                              }), uu____11841)
                             in
                          FStar_Syntax_Syntax.Tm_refine uu____11834  in
                        mk uu____11833 t1.FStar_Syntax_Syntax.pos  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
               if
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
               then
                 let uu____11871 = closure_as_term cfg env t1  in
                 rebuild cfg env stack uu____11871
               else
                 (let uu____11874 = FStar_Syntax_Subst.open_comp bs c  in
                  match uu____11874 with
                  | (bs1,c1) ->
                      let c2 =
                        let uu____11882 =
                          FStar_All.pipe_right bs1
                            (FStar_List.fold_left
                               (fun env1  ->
                                  fun uu____11908  -> dummy :: env1) env)
                           in
                        norm_comp cfg uu____11882 c1  in
                      let t2 =
                        let uu____11932 = norm_binders cfg env bs1  in
                        FStar_Syntax_Util.arrow uu____11932 c2  in
                      rebuild cfg env stack t2)
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) when
               (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unascribe
               -> norm cfg env stack t11
           | FStar_Syntax_Syntax.Tm_ascribed (t11,(tc,tacopt),l) ->
               (match stack with
                | (Match uu____12045)::uu____12046 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12059  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (Arg uu____12061)::uu____12062 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12073  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (App
                    (uu____12075,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_constant
                                     (FStar_Const.Const_reify );
                                   FStar_Syntax_Syntax.pos = uu____12076;
                                   FStar_Syntax_Syntax.vars = uu____12077;_},uu____12078,uu____12079))::uu____12080
                    when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12087  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | (MemoLazy uu____12089)::uu____12090 when
                    (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.beta
                    ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12101  ->
                          FStar_Util.print_string
                            "+++ Dropping ascription \n");
                     norm cfg env stack t11)
                | uu____12103 ->
                    (FStar_TypeChecker_Cfg.log cfg
                       (fun uu____12106  ->
                          FStar_Util.print_string "+++ Keeping ascription \n");
                     (let t12 = norm cfg env [] t11  in
                      FStar_TypeChecker_Cfg.log cfg
                        (fun uu____12111  ->
                           FStar_Util.print_string
                             "+++ Normalizing ascription \n");
                      (let tc1 =
                         match tc with
                         | FStar_Util.Inl t2 ->
                             let uu____12137 = norm cfg env [] t2  in
                             FStar_Util.Inl uu____12137
                         | FStar_Util.Inr c ->
                             let uu____12151 = norm_comp cfg env c  in
                             FStar_Util.Inr uu____12151
                          in
                       let tacopt1 =
                         FStar_Util.map_opt tacopt (norm cfg env [])  in
                       match stack with
                       | (Cfg cfg1)::stack1 ->
                           let t2 =
                             let uu____12174 =
                               let uu____12175 =
                                 let uu____12202 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12202, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12175
                                in
                             mk uu____12174 t1.FStar_Syntax_Syntax.pos  in
                           norm cfg1 env stack1 t2
                       | uu____12237 ->
                           let uu____12238 =
                             let uu____12239 =
                               let uu____12240 =
                                 let uu____12267 =
                                   FStar_Syntax_Util.unascribe t12  in
                                 (uu____12267, (tc1, tacopt1), l)  in
                               FStar_Syntax_Syntax.Tm_ascribed uu____12240
                                in
                             mk uu____12239 t1.FStar_Syntax_Syntax.pos  in
                           rebuild cfg env stack uu____12238))))
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
                   let uu___1556_12345 = cfg  in
                   {
                     FStar_TypeChecker_Cfg.steps =
                       (let uu___1558_12348 = cfg.FStar_TypeChecker_Cfg.steps
                           in
                        {
                          FStar_TypeChecker_Cfg.beta =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.beta);
                          FStar_TypeChecker_Cfg.iota =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.iota);
                          FStar_TypeChecker_Cfg.zeta =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.zeta);
                          FStar_TypeChecker_Cfg.weak = true;
                          FStar_TypeChecker_Cfg.hnf =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.hnf);
                          FStar_TypeChecker_Cfg.primops =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.primops);
                          FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                          FStar_TypeChecker_Cfg.unfold_until =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.unfold_until);
                          FStar_TypeChecker_Cfg.unfold_only =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.unfold_only);
                          FStar_TypeChecker_Cfg.unfold_fully =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.unfold_fully);
                          FStar_TypeChecker_Cfg.unfold_attr =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.unfold_attr);
                          FStar_TypeChecker_Cfg.unfold_tac =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.unfold_tac);
                          FStar_TypeChecker_Cfg.pure_subterms_within_computations
                            =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                          FStar_TypeChecker_Cfg.simplify =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.simplify);
                          FStar_TypeChecker_Cfg.erase_universes =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.erase_universes);
                          FStar_TypeChecker_Cfg.allow_unbound_universes =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.allow_unbound_universes);
                          FStar_TypeChecker_Cfg.reify_ =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.reify_);
                          FStar_TypeChecker_Cfg.compress_uvars =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.compress_uvars);
                          FStar_TypeChecker_Cfg.no_full_norm =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.no_full_norm);
                          FStar_TypeChecker_Cfg.check_no_uvars =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.check_no_uvars);
                          FStar_TypeChecker_Cfg.unmeta =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.unmeta);
                          FStar_TypeChecker_Cfg.unascribe =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.unascribe);
                          FStar_TypeChecker_Cfg.in_full_norm_request =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.in_full_norm_request);
                          FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                          FStar_TypeChecker_Cfg.nbe_step =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.nbe_step);
                          FStar_TypeChecker_Cfg.for_extraction =
                            (uu___1558_12348.FStar_TypeChecker_Cfg.for_extraction)
                        });
                     FStar_TypeChecker_Cfg.tcenv =
                       (uu___1556_12345.FStar_TypeChecker_Cfg.tcenv);
                     FStar_TypeChecker_Cfg.debug =
                       (uu___1556_12345.FStar_TypeChecker_Cfg.debug);
                     FStar_TypeChecker_Cfg.delta_level =
                       (uu___1556_12345.FStar_TypeChecker_Cfg.delta_level);
                     FStar_TypeChecker_Cfg.primitive_steps =
                       (uu___1556_12345.FStar_TypeChecker_Cfg.primitive_steps);
                     FStar_TypeChecker_Cfg.strong =
                       (uu___1556_12345.FStar_TypeChecker_Cfg.strong);
                     FStar_TypeChecker_Cfg.memoize_lazy =
                       (uu___1556_12345.FStar_TypeChecker_Cfg.memoize_lazy);
                     FStar_TypeChecker_Cfg.normalize_pure_lets =
                       (uu___1556_12345.FStar_TypeChecker_Cfg.normalize_pure_lets);
                     FStar_TypeChecker_Cfg.reifying =
                       (uu___1556_12345.FStar_TypeChecker_Cfg.reifying)
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
                         let uu____12389 =
                           FStar_Syntax_Subst.univ_var_opening
                             lb.FStar_Syntax_Syntax.lbunivs
                            in
                         match uu____12389 with
                         | (openings,lbunivs) ->
                             let cfg1 =
                               let uu___1571_12409 = cfg  in
                               let uu____12410 =
                                 FStar_TypeChecker_Env.push_univ_vars
                                   cfg.FStar_TypeChecker_Cfg.tcenv lbunivs
                                  in
                               {
                                 FStar_TypeChecker_Cfg.steps =
                                   (uu___1571_12409.FStar_TypeChecker_Cfg.steps);
                                 FStar_TypeChecker_Cfg.tcenv = uu____12410;
                                 FStar_TypeChecker_Cfg.debug =
                                   (uu___1571_12409.FStar_TypeChecker_Cfg.debug);
                                 FStar_TypeChecker_Cfg.delta_level =
                                   (uu___1571_12409.FStar_TypeChecker_Cfg.delta_level);
                                 FStar_TypeChecker_Cfg.primitive_steps =
                                   (uu___1571_12409.FStar_TypeChecker_Cfg.primitive_steps);
                                 FStar_TypeChecker_Cfg.strong =
                                   (uu___1571_12409.FStar_TypeChecker_Cfg.strong);
                                 FStar_TypeChecker_Cfg.memoize_lazy =
                                   (uu___1571_12409.FStar_TypeChecker_Cfg.memoize_lazy);
                                 FStar_TypeChecker_Cfg.normalize_pure_lets =
                                   (uu___1571_12409.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                 FStar_TypeChecker_Cfg.reifying =
                                   (uu___1571_12409.FStar_TypeChecker_Cfg.reifying)
                               }  in
                             let norm1 t2 =
                               let uu____12417 =
                                 let uu____12418 =
                                   FStar_Syntax_Subst.subst openings t2  in
                                 norm cfg1 env [] uu____12418  in
                               FStar_Syntax_Subst.close_univ_vars lbunivs
                                 uu____12417
                                in
                             let lbtyp = norm1 lb.FStar_Syntax_Syntax.lbtyp
                                in
                             let lbdef = norm1 lb.FStar_Syntax_Syntax.lbdef
                                in
                             let uu___1578_12421 = lb  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___1578_12421.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs = lbunivs;
                               FStar_Syntax_Syntax.lbtyp = lbtyp;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1578_12421.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = lbdef;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1578_12421.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1578_12421.FStar_Syntax_Syntax.lbpos)
                             }))
                  in
               let uu____12422 =
                 mk (FStar_Syntax_Syntax.Tm_let ((b, lbs1), lbody))
                   t1.FStar_Syntax_Syntax.pos
                  in
               rebuild cfg env stack uu____12422
           | FStar_Syntax_Syntax.Tm_let
               ((uu____12435,{
                               FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                                 uu____12436;
                               FStar_Syntax_Syntax.lbunivs = uu____12437;
                               FStar_Syntax_Syntax.lbtyp = uu____12438;
                               FStar_Syntax_Syntax.lbeff = uu____12439;
                               FStar_Syntax_Syntax.lbdef = uu____12440;
                               FStar_Syntax_Syntax.lbattrs = uu____12441;
                               FStar_Syntax_Syntax.lbpos = uu____12442;_}::uu____12443),uu____12444)
               -> rebuild cfg env stack t1
           | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
               let n1 =
                 FStar_TypeChecker_Env.norm_eff_name
                   cfg.FStar_TypeChecker_Cfg.tcenv
                   lb.FStar_Syntax_Syntax.lbeff
                  in
               let uu____12490 =
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
               if uu____12490
               then
                 let binder =
                   let uu____12494 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   FStar_Syntax_Syntax.mk_binder uu____12494  in
                 let env1 =
                   let uu____12504 =
                     let uu____12511 =
                       let uu____12512 =
                         let uu____12544 =
                           FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                         (env, (lb.FStar_Syntax_Syntax.lbdef), uu____12544,
                           false)
                          in
                       Clos uu____12512  in
                     ((FStar_Pervasives_Native.Some binder), uu____12511)  in
                   uu____12504 :: env  in
                 (FStar_TypeChecker_Cfg.log cfg
                    (fun uu____12619  ->
                       FStar_Util.print_string "+++ Reducing Tm_let\n");
                  norm cfg env1 stack body)
               else
                 if
                   (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.weak
                 then
                   (FStar_TypeChecker_Cfg.log cfg
                      (fun uu____12626  ->
                         FStar_Util.print_string "+++ Not touching Tm_let\n");
                    (let uu____12628 = closure_as_term cfg env t1  in
                     rebuild cfg env stack uu____12628))
                 else
                   (let uu____12631 =
                      let uu____12636 =
                        let uu____12637 =
                          let uu____12644 =
                            FStar_All.pipe_right
                              lb.FStar_Syntax_Syntax.lbname FStar_Util.left
                             in
                          FStar_All.pipe_right uu____12644
                            FStar_Syntax_Syntax.mk_binder
                           in
                        [uu____12637]  in
                      FStar_Syntax_Subst.open_term uu____12636 body  in
                    match uu____12631 with
                    | (bs,body1) ->
                        (FStar_TypeChecker_Cfg.log cfg
                           (fun uu____12671  ->
                              FStar_Util.print_string
                                "+++ Normalizing Tm_let -- type");
                         (let ty =
                            norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                          let lbname =
                            let x =
                              let uu____12680 = FStar_List.hd bs  in
                              FStar_Pervasives_Native.fst uu____12680  in
                            FStar_Util.Inl
                              (let uu___1620_12696 = x  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1620_12696.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1620_12696.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               })
                             in
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____12699  ->
                               FStar_Util.print_string
                                 "+++ Normalizing Tm_let -- definiens\n");
                          (let lb1 =
                             let uu___1625_12702 = lb  in
                             let uu____12703 =
                               norm cfg env [] lb.FStar_Syntax_Syntax.lbdef
                                in
                             {
                               FStar_Syntax_Syntax.lbname = lbname;
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___1625_12702.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp = ty;
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___1625_12702.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____12703;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___1625_12702.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___1625_12702.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let env' =
                             FStar_All.pipe_right bs
                               (FStar_List.fold_left
                                  (fun env1  ->
                                     fun uu____12732  -> dummy :: env1) env)
                              in
                           let stack1 = (Cfg cfg) :: stack  in
                           let cfg1 =
                             let uu___1632_12757 = cfg  in
                             {
                               FStar_TypeChecker_Cfg.steps =
                                 (uu___1632_12757.FStar_TypeChecker_Cfg.steps);
                               FStar_TypeChecker_Cfg.tcenv =
                                 (uu___1632_12757.FStar_TypeChecker_Cfg.tcenv);
                               FStar_TypeChecker_Cfg.debug =
                                 (uu___1632_12757.FStar_TypeChecker_Cfg.debug);
                               FStar_TypeChecker_Cfg.delta_level =
                                 (uu___1632_12757.FStar_TypeChecker_Cfg.delta_level);
                               FStar_TypeChecker_Cfg.primitive_steps =
                                 (uu___1632_12757.FStar_TypeChecker_Cfg.primitive_steps);
                               FStar_TypeChecker_Cfg.strong = true;
                               FStar_TypeChecker_Cfg.memoize_lazy =
                                 (uu___1632_12757.FStar_TypeChecker_Cfg.memoize_lazy);
                               FStar_TypeChecker_Cfg.normalize_pure_lets =
                                 (uu___1632_12757.FStar_TypeChecker_Cfg.normalize_pure_lets);
                               FStar_TypeChecker_Cfg.reifying =
                                 (uu___1632_12757.FStar_TypeChecker_Cfg.reifying)
                             }  in
                           FStar_TypeChecker_Cfg.log cfg1
                             (fun uu____12761  ->
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
               let uu____12782 = FStar_Syntax_Subst.open_let_rec lbs body  in
               (match uu____12782 with
                | (lbs1,body1) ->
                    let lbs2 =
                      FStar_List.map
                        (fun lb  ->
                           let ty =
                             norm cfg env [] lb.FStar_Syntax_Syntax.lbtyp  in
                           let lbname =
                             let uu____12818 =
                               let uu___1648_12819 =
                                 FStar_Util.left
                                   lb.FStar_Syntax_Syntax.lbname
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1648_12819.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1648_12819.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = ty
                               }  in
                             FStar_Util.Inl uu____12818  in
                           let uu____12820 =
                             FStar_Syntax_Util.abs_formals
                               lb.FStar_Syntax_Syntax.lbdef
                              in
                           match uu____12820 with
                           | (xs,def_body,lopt) ->
                               let xs1 = norm_binders cfg env xs  in
                               let env1 =
                                 let uu____12846 =
                                   FStar_List.map (fun uu____12862  -> dummy)
                                     lbs1
                                    in
                                 let uu____12863 =
                                   let uu____12872 =
                                     FStar_List.map
                                       (fun uu____12894  -> dummy) xs1
                                      in
                                   FStar_List.append uu____12872 env  in
                                 FStar_List.append uu____12846 uu____12863
                                  in
                               let def_body1 = norm cfg env1 [] def_body  in
                               let lopt1 =
                                 match lopt with
                                 | FStar_Pervasives_Native.Some rc ->
                                     let uu____12920 =
                                       let uu___1662_12921 = rc  in
                                       let uu____12922 =
                                         FStar_Util.map_opt
                                           rc.FStar_Syntax_Syntax.residual_typ
                                           (norm cfg env1 [])
                                          in
                                       {
                                         FStar_Syntax_Syntax.residual_effect
                                           =
                                           (uu___1662_12921.FStar_Syntax_Syntax.residual_effect);
                                         FStar_Syntax_Syntax.residual_typ =
                                           uu____12922;
                                         FStar_Syntax_Syntax.residual_flags =
                                           (uu___1662_12921.FStar_Syntax_Syntax.residual_flags)
                                       }  in
                                     FStar_Pervasives_Native.Some uu____12920
                                 | uu____12931 -> lopt  in
                               let def =
                                 FStar_Syntax_Util.abs xs1 def_body1 lopt1
                                  in
                               let uu___1667_12937 = lb  in
                               {
                                 FStar_Syntax_Syntax.lbname = lbname;
                                 FStar_Syntax_Syntax.lbunivs =
                                   (uu___1667_12937.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp = ty;
                                 FStar_Syntax_Syntax.lbeff =
                                   (uu___1667_12937.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef = def;
                                 FStar_Syntax_Syntax.lbattrs =
                                   (uu___1667_12937.FStar_Syntax_Syntax.lbattrs);
                                 FStar_Syntax_Syntax.lbpos =
                                   (uu___1667_12937.FStar_Syntax_Syntax.lbpos)
                               }) lbs1
                       in
                    let env' =
                      let uu____12947 =
                        FStar_List.map (fun uu____12963  -> dummy) lbs2  in
                      FStar_List.append uu____12947 env  in
                    let body2 = norm cfg env' [] body1  in
                    let uu____12971 =
                      FStar_Syntax_Subst.close_let_rec lbs2 body2  in
                    (match uu____12971 with
                     | (lbs3,body3) ->
                         let t2 =
                           let uu___1676_12987 = t1  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_let
                                  ((true, lbs3), body3));
                             FStar_Syntax_Syntax.pos =
                               (uu___1676_12987.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1676_12987.FStar_Syntax_Syntax.vars)
                           }  in
                         rebuild cfg env stack t2))
           | FStar_Syntax_Syntax.Tm_let (lbs,body) when
               Prims.op_Negation
                 (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.zeta
               ->
               let uu____13021 = closure_as_term cfg env t1  in
               rebuild cfg env stack uu____13021
           | FStar_Syntax_Syntax.Tm_let (lbs,body) ->
               let uu____13042 =
                 FStar_List.fold_right
                   (fun lb  ->
                      fun uu____13120  ->
                        match uu____13120 with
                        | (rec_env,memos,i) ->
                            let bv =
                              let uu___1692_13245 =
                                FStar_Util.left lb.FStar_Syntax_Syntax.lbname
                                 in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___1692_13245.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index = i;
                                FStar_Syntax_Syntax.sort =
                                  (uu___1692_13245.FStar_Syntax_Syntax.sort)
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
                            (rec_env1, (memo :: memos),
                              (i + (Prims.parse_int "1"))))
                   (FStar_Pervasives_Native.snd lbs)
                   (env, [], (Prims.parse_int "0"))
                  in
               (match uu____13042 with
                | (rec_env,memos,uu____13436) ->
                    let uu____13491 =
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
                             let uu____13740 =
                               let uu____13747 =
                                 let uu____13748 =
                                   let uu____13780 =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (rec_env, (lb.FStar_Syntax_Syntax.lbdef),
                                     uu____13780, false)
                                    in
                                 Clos uu____13748  in
                               (FStar_Pervasives_Native.None, uu____13747)
                                in
                             uu____13740 :: env1)
                        (FStar_Pervasives_Native.snd lbs) env
                       in
                    norm cfg body_env stack body)
           | FStar_Syntax_Syntax.Tm_meta (head1,m) ->
               (FStar_TypeChecker_Cfg.log cfg
                  (fun uu____13865  ->
                     let uu____13866 =
                       FStar_Syntax_Print.metadata_to_string m  in
                     FStar_Util.print1 ">> metadata = %s\n" uu____13866);
                (match m with
                 | FStar_Syntax_Syntax.Meta_monadic (m1,t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inl m1) t2
                 | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m',t2) ->
                     reduce_impure_comp cfg env stack head1
                       (FStar_Util.Inr (m1, m')) t2
                 | uu____13890 ->
                     if
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.unmeta
                     then norm cfg env stack head1
                     else
                       (match stack with
                        | uu____13894::uu____13895 ->
                            (match m with
                             | FStar_Syntax_Syntax.Meta_labeled
                                 (l,r,uu____13900) ->
                                 norm cfg env ((Meta (env, m, r)) :: stack)
                                   head1
                             | FStar_Syntax_Syntax.Meta_pattern
                                 (names1,args,np) ->
                                 let args1 = norm_pattern_args cfg env args
                                    in
                                 let names2 =
                                   FStar_All.pipe_right names1
                                     (FStar_List.map (norm cfg env []))
                                    in
                                 let args2 =
                                   FStar_TypeChecker_PatternInference.remove_invalid_pattern
                                     names2 args1
                                    in
                                 norm cfg env
                                   ((Meta
                                       (env,
                                         (FStar_Syntax_Syntax.Meta_pattern
                                            (names2, args2, np)),
                                         (t1.FStar_Syntax_Syntax.pos))) ::
                                   stack) head1
                             | uu____13986 -> norm cfg env stack head1)
                        | [] ->
                            let head2 = norm cfg env [] head1  in
                            let m1 =
                              match m with
                              | FStar_Syntax_Syntax.Meta_pattern
                                  (names1,args,np) ->
                                  let names2 =
                                    FStar_All.pipe_right names1
                                      (FStar_List.map (norm cfg env []))
                                     in
                                  let uu____14037 =
                                    let uu____14061 =
                                      norm_pattern_args cfg env args  in
                                    (names2, uu____14061, np)  in
                                  FStar_Syntax_Syntax.Meta_pattern
                                    uu____14037
                              | uu____14091 -> m  in
                            let t2 =
                              mk (FStar_Syntax_Syntax.Tm_meta (head2, m1))
                                t1.FStar_Syntax_Syntax.pos
                               in
                            rebuild cfg env stack t2)))
           | FStar_Syntax_Syntax.Tm_delayed uu____14097 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               norm cfg env stack t2
           | FStar_Syntax_Syntax.Tm_uvar uu____14121 ->
               let t2 = FStar_Syntax_Subst.compress t1  in
               (match t2.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_uvar uu____14135 ->
                    if
                      (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.check_no_uvars
                    then
                      let uu____14149 =
                        let uu____14151 =
                          FStar_Range.string_of_range
                            t2.FStar_Syntax_Syntax.pos
                           in
                        let uu____14153 =
                          FStar_Syntax_Print.term_to_string t2  in
                        FStar_Util.format2
                          "(%s) CheckNoUvars: Unexpected unification variable remains: %s"
                          uu____14151 uu____14153
                         in
                      failwith uu____14149
                    else
                      (let uu____14158 = inline_closure_env cfg env [] t2  in
                       rebuild cfg env stack uu____14158)
                | uu____14159 -> norm cfg env stack t2))

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
              let uu____14168 =
                FStar_TypeChecker_Env.lookup_definition_qninfo
                  cfg.FStar_TypeChecker_Cfg.delta_level
                  (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  qninfo
                 in
              match uu____14168 with
              | FStar_Pervasives_Native.None  ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14182  ->
                        let uu____14183 = FStar_Syntax_Print.fv_to_string f
                           in
                        FStar_Util.print1 " >> Tm_fvar case 2 for %s\n"
                          uu____14183);
                   rebuild cfg env stack t0)
              | FStar_Pervasives_Native.Some (us,t) ->
                  (FStar_TypeChecker_Cfg.log_unfolding cfg
                     (fun uu____14196  ->
                        let uu____14197 =
                          FStar_Syntax_Print.term_to_string t0  in
                        let uu____14199 = FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print2 " >> Unfolded %s to %s\n"
                          uu____14197 uu____14199);
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
                    if n1 > (Prims.parse_int "0")
                    then
                      match stack with
                      | (UnivArgs (us',uu____14212))::stack1 ->
                          ((let uu____14221 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug
                                   cfg.FStar_TypeChecker_Cfg.tcenv)
                                (FStar_Options.Other "univ_norm")
                               in
                            if uu____14221
                            then
                              FStar_List.iter
                                (fun x  ->
                                   let uu____14229 =
                                     FStar_Syntax_Print.univ_to_string x  in
                                   FStar_Util.print1 "Univ (normalizer) %s\n"
                                     uu____14229) us'
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
                      | uu____14265 when
                          (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.erase_universes
                            ||
                            (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.allow_unbound_universes
                          -> norm cfg env stack t1
                      | uu____14268 ->
                          let uu____14271 =
                            let uu____14273 =
                              FStar_Syntax_Print.lid_to_string
                                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            FStar_Util.format1
                              "Impossible: missing universe instantiation on %s"
                              uu____14273
                             in
                          failwith uu____14271
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
                  let uu___1807_14301 = cfg  in
                  let uu____14302 =
                    FStar_List.fold_right FStar_TypeChecker_Cfg.fstep_add_one
                      new_steps cfg.FStar_TypeChecker_Cfg.steps
                     in
                  {
                    FStar_TypeChecker_Cfg.steps = uu____14302;
                    FStar_TypeChecker_Cfg.tcenv =
                      (uu___1807_14301.FStar_TypeChecker_Cfg.tcenv);
                    FStar_TypeChecker_Cfg.debug =
                      (uu___1807_14301.FStar_TypeChecker_Cfg.debug);
                    FStar_TypeChecker_Cfg.delta_level =
                      [FStar_TypeChecker_Env.InliningDelta;
                      FStar_TypeChecker_Env.Eager_unfolding_only];
                    FStar_TypeChecker_Cfg.primitive_steps =
                      (uu___1807_14301.FStar_TypeChecker_Cfg.primitive_steps);
                    FStar_TypeChecker_Cfg.strong =
                      (uu___1807_14301.FStar_TypeChecker_Cfg.strong);
                    FStar_TypeChecker_Cfg.memoize_lazy =
                      (uu___1807_14301.FStar_TypeChecker_Cfg.memoize_lazy);
                    FStar_TypeChecker_Cfg.normalize_pure_lets =
                      (uu___1807_14301.FStar_TypeChecker_Cfg.normalize_pure_lets);
                    FStar_TypeChecker_Cfg.reifying =
                      (uu___1807_14301.FStar_TypeChecker_Cfg.reifying)
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
                     (uu____14333,{
                                    FStar_Syntax_Syntax.n =
                                      FStar_Syntax_Syntax.Tm_constant
                                      (FStar_Const.Const_reify );
                                    FStar_Syntax_Syntax.pos = uu____14334;
                                    FStar_Syntax_Syntax.vars = uu____14335;_},uu____14336,uu____14337))::uu____14338
                     -> ()
                 | uu____14343 ->
                     let uu____14346 =
                       let uu____14348 = stack_to_string stack  in
                       FStar_Util.format1
                         "INTERNAL ERROR: do_reify_monadic: bad stack: %s"
                         uu____14348
                        in
                     failwith uu____14346);
                (let head0 = head1  in
                 let head2 = FStar_Syntax_Util.unascribe head1  in
                 FStar_TypeChecker_Cfg.log cfg
                   (fun uu____14357  ->
                      let uu____14358 = FStar_Syntax_Print.tag_of_term head2
                         in
                      let uu____14360 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print2 "Reifying: (%s) %s\n" uu____14358
                        uu____14360);
                 (let head3 = FStar_Syntax_Util.unmeta_safe head2  in
                  let uu____14364 =
                    let uu____14365 = FStar_Syntax_Subst.compress head3  in
                    uu____14365.FStar_Syntax_Syntax.n  in
                  match uu____14364 with
                  | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),body) ->
                      let ed =
                        let uu____14386 =
                          FStar_TypeChecker_Env.norm_eff_name
                            cfg.FStar_TypeChecker_Cfg.tcenv m
                           in
                        FStar_TypeChecker_Env.get_effect_decl
                          cfg.FStar_TypeChecker_Cfg.tcenv uu____14386
                         in
                      let uu____14387 = ed.FStar_Syntax_Syntax.bind_repr  in
                      (match uu____14387 with
                       | (uu____14388,bind_repr) ->
                           (match lb.FStar_Syntax_Syntax.lbname with
                            | FStar_Util.Inr uu____14398 ->
                                failwith
                                  "Cannot reify a top-level let binding"
                            | FStar_Util.Inl x ->
                                let is_return e =
                                  let uu____14409 =
                                    let uu____14410 =
                                      FStar_Syntax_Subst.compress e  in
                                    uu____14410.FStar_Syntax_Syntax.n  in
                                  match uu____14409 with
                                  | FStar_Syntax_Syntax.Tm_meta
                                      (e1,FStar_Syntax_Syntax.Meta_monadic
                                       (uu____14416,uu____14417))
                                      ->
                                      let uu____14426 =
                                        let uu____14427 =
                                          FStar_Syntax_Subst.compress e1  in
                                        uu____14427.FStar_Syntax_Syntax.n  in
                                      (match uu____14426 with
                                       | FStar_Syntax_Syntax.Tm_meta
                                           (e2,FStar_Syntax_Syntax.Meta_monadic_lift
                                            (uu____14433,msrc,uu____14435))
                                           when
                                           FStar_Syntax_Util.is_pure_effect
                                             msrc
                                           ->
                                           let uu____14444 =
                                             FStar_Syntax_Subst.compress e2
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____14444
                                       | uu____14445 ->
                                           FStar_Pervasives_Native.None)
                                  | uu____14446 ->
                                      FStar_Pervasives_Native.None
                                   in
                                let uu____14447 =
                                  is_return lb.FStar_Syntax_Syntax.lbdef  in
                                (match uu____14447 with
                                 | FStar_Pervasives_Native.Some e ->
                                     let lb1 =
                                       let uu___1879_14452 = lb  in
                                       {
                                         FStar_Syntax_Syntax.lbname =
                                           (uu___1879_14452.FStar_Syntax_Syntax.lbname);
                                         FStar_Syntax_Syntax.lbunivs =
                                           (uu___1879_14452.FStar_Syntax_Syntax.lbunivs);
                                         FStar_Syntax_Syntax.lbtyp =
                                           (uu___1879_14452.FStar_Syntax_Syntax.lbtyp);
                                         FStar_Syntax_Syntax.lbeff =
                                           FStar_Parser_Const.effect_PURE_lid;
                                         FStar_Syntax_Syntax.lbdef = e;
                                         FStar_Syntax_Syntax.lbattrs =
                                           (uu___1879_14452.FStar_Syntax_Syntax.lbattrs);
                                         FStar_Syntax_Syntax.lbpos =
                                           (uu___1879_14452.FStar_Syntax_Syntax.lbpos)
                                       }  in
                                     let uu____14453 = FStar_List.tl stack
                                        in
                                     let uu____14454 =
                                       let uu____14455 =
                                         let uu____14462 =
                                           let uu____14463 =
                                             let uu____14477 =
                                               FStar_Syntax_Util.mk_reify
                                                 body
                                                in
                                             ((false, [lb1]), uu____14477)
                                              in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____14463
                                            in
                                         FStar_Syntax_Syntax.mk uu____14462
                                          in
                                       uu____14455
                                         FStar_Pervasives_Native.None
                                         head3.FStar_Syntax_Syntax.pos
                                        in
                                     norm cfg env uu____14453 uu____14454
                                 | FStar_Pervasives_Native.None  ->
                                     let uu____14493 =
                                       let uu____14495 = is_return body  in
                                       match uu____14495 with
                                       | FStar_Pervasives_Native.Some
                                           {
                                             FStar_Syntax_Syntax.n =
                                               FStar_Syntax_Syntax.Tm_bvar y;
                                             FStar_Syntax_Syntax.pos =
                                               uu____14500;
                                             FStar_Syntax_Syntax.vars =
                                               uu____14501;_}
                                           -> FStar_Syntax_Syntax.bv_eq x y
                                       | uu____14504 -> false  in
                                     if uu____14493
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
                                          let uu____14528 =
                                            let uu____14535 =
                                              let uu____14536 =
                                                let uu____14555 =
                                                  let uu____14564 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      x
                                                     in
                                                  [uu____14564]  in
                                                (uu____14555, body1,
                                                  (FStar_Pervasives_Native.Some
                                                     body_rc))
                                                 in
                                              FStar_Syntax_Syntax.Tm_abs
                                                uu____14536
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____14535
                                             in
                                          uu____14528
                                            FStar_Pervasives_Native.None
                                            body1.FStar_Syntax_Syntax.pos
                                           in
                                        let close1 = closure_as_term cfg env
                                           in
                                        let bind_inst =
                                          let uu____14603 =
                                            let uu____14604 =
                                              FStar_Syntax_Subst.compress
                                                bind_repr
                                               in
                                            uu____14604.FStar_Syntax_Syntax.n
                                             in
                                          match uu____14603 with
                                          | FStar_Syntax_Syntax.Tm_uinst
                                              (bind1,uu____14610::uu____14611::[])
                                              ->
                                              let uu____14616 =
                                                let uu____14623 =
                                                  let uu____14624 =
                                                    let uu____14631 =
                                                      let uu____14632 =
                                                        let uu____14633 =
                                                          close1
                                                            lb.FStar_Syntax_Syntax.lbtyp
                                                           in
                                                        (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                          cfg.FStar_TypeChecker_Cfg.tcenv
                                                          uu____14633
                                                         in
                                                      let uu____14634 =
                                                        let uu____14637 =
                                                          let uu____14638 =
                                                            close1 t  in
                                                          (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.universe_of
                                                            cfg.FStar_TypeChecker_Cfg.tcenv
                                                            uu____14638
                                                           in
                                                        [uu____14637]  in
                                                      uu____14632 ::
                                                        uu____14634
                                                       in
                                                    (bind1, uu____14631)  in
                                                  FStar_Syntax_Syntax.Tm_uinst
                                                    uu____14624
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____14623
                                                 in
                                              uu____14616
                                                FStar_Pervasives_Native.None
                                                rng
                                          | uu____14641 ->
                                              failwith
                                                "NIY : Reification of indexed effects"
                                           in
                                        let maybe_range_arg =
                                          let uu____14656 =
                                            FStar_Util.for_some
                                              (FStar_Syntax_Util.attr_eq
                                                 FStar_Syntax_Util.dm4f_bind_range_attr)
                                              ed.FStar_Syntax_Syntax.eff_attrs
                                             in
                                          if uu____14656
                                          then
                                            let uu____14669 =
                                              let uu____14678 =
                                                FStar_TypeChecker_Cfg.embed_simple
                                                  FStar_Syntax_Embeddings.e_range
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                  lb.FStar_Syntax_Syntax.lbpos
                                                 in
                                              FStar_Syntax_Syntax.as_arg
                                                uu____14678
                                               in
                                            let uu____14679 =
                                              let uu____14690 =
                                                let uu____14699 =
                                                  FStar_TypeChecker_Cfg.embed_simple
                                                    FStar_Syntax_Embeddings.e_range
                                                    body2.FStar_Syntax_Syntax.pos
                                                    body2.FStar_Syntax_Syntax.pos
                                                   in
                                                FStar_Syntax_Syntax.as_arg
                                                  uu____14699
                                                 in
                                              [uu____14690]  in
                                            uu____14669 :: uu____14679
                                          else []  in
                                        let reified =
                                          let uu____14737 =
                                            let uu____14744 =
                                              let uu____14745 =
                                                let uu____14762 =
                                                  let uu____14773 =
                                                    let uu____14784 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        lb.FStar_Syntax_Syntax.lbtyp
                                                       in
                                                    let uu____14793 =
                                                      let uu____14804 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          t
                                                         in
                                                      [uu____14804]  in
                                                    uu____14784 ::
                                                      uu____14793
                                                     in
                                                  let uu____14837 =
                                                    let uu____14848 =
                                                      let uu____14859 =
                                                        FStar_Syntax_Syntax.as_arg
                                                          FStar_Syntax_Syntax.tun
                                                         in
                                                      let uu____14868 =
                                                        let uu____14879 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            head4
                                                           in
                                                        let uu____14888 =
                                                          let uu____14899 =
                                                            FStar_Syntax_Syntax.as_arg
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let uu____14908 =
                                                            let uu____14919 =
                                                              FStar_Syntax_Syntax.as_arg
                                                                body2
                                                               in
                                                            [uu____14919]  in
                                                          uu____14899 ::
                                                            uu____14908
                                                           in
                                                        uu____14879 ::
                                                          uu____14888
                                                         in
                                                      uu____14859 ::
                                                        uu____14868
                                                       in
                                                    FStar_List.append
                                                      maybe_range_arg
                                                      uu____14848
                                                     in
                                                  FStar_List.append
                                                    uu____14773 uu____14837
                                                   in
                                                (bind_inst, uu____14762)  in
                                              FStar_Syntax_Syntax.Tm_app
                                                uu____14745
                                               in
                                            FStar_Syntax_Syntax.mk
                                              uu____14744
                                             in
                                          uu____14737
                                            FStar_Pervasives_Native.None rng
                                           in
                                        FStar_TypeChecker_Cfg.log cfg
                                          (fun uu____15000  ->
                                             let uu____15001 =
                                               FStar_Syntax_Print.term_to_string
                                                 head0
                                                in
                                             let uu____15003 =
                                               FStar_Syntax_Print.term_to_string
                                                 reified
                                                in
                                             FStar_Util.print2
                                               "Reified (1) <%s> to %s\n"
                                               uu____15001 uu____15003);
                                        (let uu____15006 =
                                           FStar_List.tl stack  in
                                         norm cfg env uu____15006 reified)))))
                  | FStar_Syntax_Syntax.Tm_app (head_app,args) ->
                      ((let uu____15034 = FStar_Options.defensive ()  in
                        if uu____15034
                        then
                          let is_arg_impure uu____15049 =
                            match uu____15049 with
                            | (e,q) ->
                                let uu____15063 =
                                  let uu____15064 =
                                    FStar_Syntax_Subst.compress e  in
                                  uu____15064.FStar_Syntax_Syntax.n  in
                                (match uu____15063 with
                                 | FStar_Syntax_Syntax.Tm_meta
                                     (e0,FStar_Syntax_Syntax.Meta_monadic_lift
                                      (m1,m2,t'))
                                     ->
                                     let uu____15080 =
                                       FStar_Syntax_Util.is_pure_effect m1
                                        in
                                     Prims.op_Negation uu____15080
                                 | uu____15082 -> false)
                             in
                          let uu____15084 =
                            let uu____15086 =
                              let uu____15097 =
                                FStar_Syntax_Syntax.as_arg head_app  in
                              uu____15097 :: args  in
                            FStar_Util.for_some is_arg_impure uu____15086  in
                          (if uu____15084
                           then
                             let uu____15123 =
                               let uu____15129 =
                                 let uu____15131 =
                                   FStar_Syntax_Print.term_to_string head3
                                    in
                                 FStar_Util.format1
                                   "Incompatibility between typechecker and normalizer; this monadic application contains impure terms %s\n"
                                   uu____15131
                                  in
                               (FStar_Errors.Warning_Defensive, uu____15129)
                                in
                             FStar_Errors.log_issue
                               head3.FStar_Syntax_Syntax.pos uu____15123
                           else ())
                        else ());
                       (let fallback1 uu____15144 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15148  ->
                               let uu____15149 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (2) <%s> to %s\n"
                                 uu____15149 "");
                          (let uu____15153 = FStar_List.tl stack  in
                           let uu____15154 = FStar_Syntax_Util.mk_reify head3
                              in
                           norm cfg env uu____15153 uu____15154)
                           in
                        let fallback2 uu____15160 =
                          FStar_TypeChecker_Cfg.log cfg
                            (fun uu____15164  ->
                               let uu____15165 =
                                 FStar_Syntax_Print.term_to_string head0  in
                               FStar_Util.print2 "Reified (3) <%s> to %s\n"
                                 uu____15165 "");
                          (let uu____15169 = FStar_List.tl stack  in
                           let uu____15170 =
                             mk
                               (FStar_Syntax_Syntax.Tm_meta
                                  (head3,
                                    (FStar_Syntax_Syntax.Meta_monadic (m, t))))
                               head0.FStar_Syntax_Syntax.pos
                              in
                           norm cfg env uu____15169 uu____15170)
                           in
                        let uu____15175 =
                          let uu____15176 =
                            FStar_Syntax_Util.un_uinst head_app  in
                          uu____15176.FStar_Syntax_Syntax.n  in
                        match uu____15175 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            let lid = FStar_Syntax_Syntax.lid_of_fv fv  in
                            let qninfo =
                              FStar_TypeChecker_Env.lookup_qname
                                cfg.FStar_TypeChecker_Cfg.tcenv lid
                               in
                            let uu____15182 =
                              let uu____15184 =
                                FStar_TypeChecker_Env.is_action
                                  cfg.FStar_TypeChecker_Cfg.tcenv lid
                                 in
                              Prims.op_Negation uu____15184  in
                            if uu____15182
                            then fallback1 ()
                            else
                              (let uu____15189 =
                                 let uu____15191 =
                                   FStar_TypeChecker_Env.lookup_definition_qninfo
                                     cfg.FStar_TypeChecker_Cfg.delta_level
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                     qninfo
                                    in
                                 FStar_Option.isNone uu____15191  in
                               if uu____15189
                               then fallback2 ()
                               else
                                 (let t1 =
                                    let uu____15208 =
                                      let uu____15213 =
                                        FStar_Syntax_Util.mk_reify head_app
                                         in
                                      FStar_Syntax_Syntax.mk_Tm_app
                                        uu____15213 args
                                       in
                                    uu____15208 FStar_Pervasives_Native.None
                                      t.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____15214 = FStar_List.tl stack  in
                                  norm cfg env uu____15214 t1))
                        | uu____15215 -> fallback1 ()))
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic uu____15217) ->
                      do_reify_monadic fallback cfg env stack e m t
                  | FStar_Syntax_Syntax.Tm_meta
                      (e,FStar_Syntax_Syntax.Meta_monadic_lift
                       (msrc,mtgt,t'))
                      ->
                      let lifted =
                        let uu____15241 = closure_as_term cfg env t'  in
                        reify_lift cfg e msrc mtgt uu____15241  in
                      (FStar_TypeChecker_Cfg.log cfg
                         (fun uu____15245  ->
                            let uu____15246 =
                              FStar_Syntax_Print.term_to_string lifted  in
                            FStar_Util.print1 "Reified lift to (2): %s\n"
                              uu____15246);
                       (let uu____15249 = FStar_List.tl stack  in
                        norm cfg env uu____15249 lifted))
                  | FStar_Syntax_Syntax.Tm_match (e,branches) ->
                      let branches1 =
                        FStar_All.pipe_right branches
                          (FStar_List.map
                             (fun uu____15370  ->
                                match uu____15370 with
                                | (pat,wopt,tm) ->
                                    let uu____15418 =
                                      FStar_Syntax_Util.mk_reify tm  in
                                    (pat, wopt, uu____15418)))
                         in
                      let tm =
                        mk (FStar_Syntax_Syntax.Tm_match (e, branches1))
                          head3.FStar_Syntax_Syntax.pos
                         in
                      let uu____15450 = FStar_List.tl stack  in
                      norm cfg env uu____15450 tm
                  | uu____15451 -> fallback ()))

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
              (fun uu____15465  ->
                 let uu____15466 = FStar_Ident.string_of_lid msrc  in
                 let uu____15468 = FStar_Ident.string_of_lid mtgt  in
                 let uu____15470 = FStar_Syntax_Print.term_to_string e  in
                 FStar_Util.print3 "Reifying lift %s -> %s: %s\n" uu____15466
                   uu____15468 uu____15470);
            (let uu____15473 =
               (FStar_Syntax_Util.is_pure_effect msrc) ||
                 (FStar_Syntax_Util.is_div_effect msrc)
                in
             if uu____15473
             then
               let ed =
                 let uu____15477 =
                   FStar_TypeChecker_Env.norm_eff_name
                     cfg.FStar_TypeChecker_Cfg.tcenv mtgt
                    in
                 FStar_TypeChecker_Env.get_effect_decl env uu____15477  in
               let uu____15478 = ed.FStar_Syntax_Syntax.return_repr  in
               match uu____15478 with
               | (uu____15479,return_repr) ->
                   let return_inst =
                     let uu____15492 =
                       let uu____15493 =
                         FStar_Syntax_Subst.compress return_repr  in
                       uu____15493.FStar_Syntax_Syntax.n  in
                     match uu____15492 with
                     | FStar_Syntax_Syntax.Tm_uinst
                         (return_tm,uu____15499::[]) ->
                         let uu____15504 =
                           let uu____15511 =
                             let uu____15512 =
                               let uu____15519 =
                                 let uu____15520 =
                                   env.FStar_TypeChecker_Env.universe_of env
                                     t
                                    in
                                 [uu____15520]  in
                               (return_tm, uu____15519)  in
                             FStar_Syntax_Syntax.Tm_uinst uu____15512  in
                           FStar_Syntax_Syntax.mk uu____15511  in
                         uu____15504 FStar_Pervasives_Native.None
                           e.FStar_Syntax_Syntax.pos
                     | uu____15523 ->
                         failwith "NIY : Reification of indexed effects"
                      in
                   let uu____15527 =
                     let uu____15534 =
                       let uu____15535 =
                         let uu____15552 =
                           let uu____15563 = FStar_Syntax_Syntax.as_arg t  in
                           let uu____15572 =
                             let uu____15583 = FStar_Syntax_Syntax.as_arg e
                                in
                             [uu____15583]  in
                           uu____15563 :: uu____15572  in
                         (return_inst, uu____15552)  in
                       FStar_Syntax_Syntax.Tm_app uu____15535  in
                     FStar_Syntax_Syntax.mk uu____15534  in
                   uu____15527 FStar_Pervasives_Native.None
                     e.FStar_Syntax_Syntax.pos
             else
               (let uu____15630 =
                  FStar_TypeChecker_Env.monad_leq env msrc mtgt  in
                match uu____15630 with
                | FStar_Pervasives_Native.None  ->
                    let uu____15633 =
                      let uu____15635 = FStar_Ident.text_of_lid msrc  in
                      let uu____15637 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a lift between unrelated effects (%s and %s)"
                        uu____15635 uu____15637
                       in
                    failwith uu____15633
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15640;
                      FStar_TypeChecker_Env.mtarget = uu____15641;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15642;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.None ;_};_}
                    ->
                    let uu____15664 =
                      let uu____15666 = FStar_Ident.text_of_lid msrc  in
                      let uu____15668 = FStar_Ident.text_of_lid mtgt  in
                      FStar_Util.format2
                        "Impossible : trying to reify a non-reifiable lift (from %s to %s)"
                        uu____15666 uu____15668
                       in
                    failwith uu____15664
                | FStar_Pervasives_Native.Some
                    { FStar_TypeChecker_Env.msource = uu____15671;
                      FStar_TypeChecker_Env.mtarget = uu____15672;
                      FStar_TypeChecker_Env.mlift =
                        { FStar_TypeChecker_Env.mlift_wp = uu____15673;
                          FStar_TypeChecker_Env.mlift_term =
                            FStar_Pervasives_Native.Some lift;_};_}
                    ->
                    let uu____15708 =
                      env.FStar_TypeChecker_Env.universe_of env t  in
                    let uu____15709 = FStar_Syntax_Util.mk_reify e  in
                    lift uu____15708 t FStar_Syntax_Syntax.tun uu____15709))

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
                (fun uu____15779  ->
                   match uu____15779 with
                   | (a,imp) ->
                       let uu____15798 = norm cfg env [] a  in
                       (uu____15798, imp))))

and (norm_comp :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun cfg  ->
    fun env  ->
      fun comp  ->
        FStar_TypeChecker_Cfg.log cfg
          (fun uu____15808  ->
             let uu____15809 = FStar_Syntax_Print.comp_to_string comp  in
             let uu____15811 =
               FStar_Util.string_of_int (FStar_List.length env)  in
             FStar_Util.print2 ">>> %s\nNormComp with with %s env elements"
               uu____15809 uu____15811);
        (match comp.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Total (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15837 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _15840  -> FStar_Pervasives_Native.Some _15840)
                     uu____15837
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2029_15841 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Total (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2029_15841.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2029_15841.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.GTotal (t,uopt) ->
             let t1 = norm cfg env [] t  in
             let uopt1 =
               match uopt with
               | FStar_Pervasives_Native.Some u ->
                   let uu____15863 = norm_universe cfg env u  in
                   FStar_All.pipe_left
                     (fun _15866  -> FStar_Pervasives_Native.Some _15866)
                     uu____15863
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
                in
             let uu___2040_15867 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.GTotal (t1, uopt1));
               FStar_Syntax_Syntax.pos =
                 (uu___2040_15867.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2040_15867.FStar_Syntax_Syntax.vars)
             }
         | FStar_Syntax_Syntax.Comp ct ->
             let norm_args =
               FStar_List.mapi
                 (fun idx  ->
                    fun uu____15912  ->
                      match uu____15912 with
                      | (a,i) ->
                          let uu____15932 = norm cfg env [] a  in
                          (uu____15932, i))
                in
             let effect_args = norm_args ct.FStar_Syntax_Syntax.effect_args
                in
             let flags =
               FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                 (FStar_List.map
                    (fun uu___15_15954  ->
                       match uu___15_15954 with
                       | FStar_Syntax_Syntax.DECREASES t ->
                           let uu____15958 = norm cfg env [] t  in
                           FStar_Syntax_Syntax.DECREASES uu____15958
                       | f -> f))
                in
             let comp_univs =
               FStar_List.map (norm_universe cfg env)
                 ct.FStar_Syntax_Syntax.comp_univs
                in
             let result_typ =
               norm cfg env [] ct.FStar_Syntax_Syntax.result_typ  in
             let uu___2057_15966 = comp  in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Comp
                    (let uu___2059_15969 = ct  in
                     {
                       FStar_Syntax_Syntax.comp_univs = comp_univs;
                       FStar_Syntax_Syntax.effect_name =
                         (uu___2059_15969.FStar_Syntax_Syntax.effect_name);
                       FStar_Syntax_Syntax.result_typ = result_typ;
                       FStar_Syntax_Syntax.effect_args = effect_args;
                       FStar_Syntax_Syntax.flags = flags
                     }));
               FStar_Syntax_Syntax.pos =
                 (uu___2057_15966.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars =
                 (uu___2057_15966.FStar_Syntax_Syntax.vars)
             })

and (norm_binder :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder)
  =
  fun cfg  ->
    fun env  ->
      fun b  ->
        let uu____15973 = b  in
        match uu____15973 with
        | (x,imp) ->
            let x1 =
              let uu___2067_15981 = x  in
              let uu____15982 = norm cfg env [] x.FStar_Syntax_Syntax.sort
                 in
              {
                FStar_Syntax_Syntax.ppname =
                  (uu___2067_15981.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index =
                  (uu___2067_15981.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu____15982
              }  in
            let imp1 =
              match imp with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
                  let uu____15993 =
                    let uu____15994 = closure_as_term cfg env t  in
                    FStar_Syntax_Syntax.Meta uu____15994  in
                  FStar_Pervasives_Native.Some uu____15993
              | i -> i  in
            (x1, imp1)

and (norm_binders :
  FStar_TypeChecker_Cfg.cfg ->
    env -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun cfg  ->
    fun env  ->
      fun bs  ->
        let uu____16005 =
          FStar_List.fold_left
            (fun uu____16039  ->
               fun b  ->
                 match uu____16039 with
                 | (nbs',env1) ->
                     let b1 = norm_binder cfg env1 b  in
                     ((b1 :: nbs'), (dummy :: env1))) ([], env) bs
           in
        match uu____16005 with | (nbs,uu____16119) -> FStar_List.rev nbs

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
            let uu____16151 =
              let uu___2092_16152 = rc  in
              let uu____16153 =
                FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                  (norm cfg env [])
                 in
              {
                FStar_Syntax_Syntax.residual_effect =
                  (uu___2092_16152.FStar_Syntax_Syntax.residual_effect);
                FStar_Syntax_Syntax.residual_typ = uu____16153;
                FStar_Syntax_Syntax.residual_flags =
                  (uu___2092_16152.FStar_Syntax_Syntax.residual_flags)
              }  in
            FStar_Pervasives_Native.Some uu____16151
        | uu____16162 -> lopt

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
            (let uu____16172 = FStar_Syntax_Print.term_to_string tm  in
             let uu____16174 = FStar_Syntax_Print.term_to_string tm'  in
             FStar_Util.print3 "%sSimplified\n\t%s to\n\t%s\n"
               (if
                  (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
                then ""
                else "NOT ") uu____16172 uu____16174)
          else ();
          tm'

and (norm_cb : FStar_TypeChecker_Cfg.cfg -> FStar_Syntax_Embeddings.norm_cb)
  =
  fun cfg  ->
    fun uu___16_16186  ->
      match uu___16_16186 with
      | FStar_Util.Inr x -> norm cfg [] [] x
      | FStar_Util.Inl l ->
          let uu____16199 =
            FStar_Syntax_DsEnv.try_lookup_lid
              (cfg.FStar_TypeChecker_Cfg.tcenv).FStar_TypeChecker_Env.dsenv l
             in
          (match uu____16199 with
           | FStar_Pervasives_Native.Some t -> t
           | FStar_Pervasives_Native.None  ->
               let uu____16203 =
                 FStar_Syntax_Syntax.lid_as_fv l
                   FStar_Syntax_Syntax.delta_constant
                   FStar_Pervasives_Native.None
                  in
               FStar_Syntax_Syntax.fv_to_tm uu____16203)

and (maybe_simplify_aux :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun tm  ->
          let tm1 =
            let uu____16211 = norm_cb cfg  in
            reduce_primops uu____16211 cfg env tm  in
          let uu____16216 =
            FStar_All.pipe_left Prims.op_Negation
              (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.simplify
             in
          if uu____16216
          then tm1
          else
            (let w t =
               let uu___2120_16235 = t  in
               {
                 FStar_Syntax_Syntax.n =
                   (uu___2120_16235.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = (tm1.FStar_Syntax_Syntax.pos);
                 FStar_Syntax_Syntax.vars =
                   (uu___2120_16235.FStar_Syntax_Syntax.vars)
               }  in
             let simp_t t =
               let uu____16247 =
                 let uu____16248 = FStar_Syntax_Util.unmeta t  in
                 uu____16248.FStar_Syntax_Syntax.n  in
               match uu____16247 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_Pervasives_Native.Some true
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.false_lid
                   -> FStar_Pervasives_Native.Some false
               | uu____16260 -> FStar_Pervasives_Native.None  in
             let rec args_are_binders args bs =
               match (args, bs) with
               | ((t,uu____16324)::args1,(bv,uu____16327)::bs1) ->
                   let uu____16381 =
                     let uu____16382 = FStar_Syntax_Subst.compress t  in
                     uu____16382.FStar_Syntax_Syntax.n  in
                   (match uu____16381 with
                    | FStar_Syntax_Syntax.Tm_name bv' ->
                        (FStar_Syntax_Syntax.bv_eq bv bv') &&
                          (args_are_binders args1 bs1)
                    | uu____16387 -> false)
               | ([],[]) -> true
               | (uu____16418,uu____16419) -> false  in
             let is_applied bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____16470 = FStar_Syntax_Print.term_to_string t  in
                  let uu____16472 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2 "WPE> is_applied %s -- %s\n" uu____16470
                    uu____16472)
               else ();
               (let uu____16477 = FStar_Syntax_Util.head_and_args' t  in
                match uu____16477 with
                | (hd1,args) ->
                    let uu____16516 =
                      let uu____16517 = FStar_Syntax_Subst.compress hd1  in
                      uu____16517.FStar_Syntax_Syntax.n  in
                    (match uu____16516 with
                     | FStar_Syntax_Syntax.Tm_name bv when
                         args_are_binders args bs ->
                         (if
                            (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                          then
                            (let uu____16525 =
                               FStar_Syntax_Print.term_to_string t  in
                             let uu____16527 =
                               FStar_Syntax_Print.bv_to_string bv  in
                             let uu____16529 =
                               FStar_Syntax_Print.term_to_string hd1  in
                             FStar_Util.print3
                               "WPE> got it\n>>>>top = %s\n>>>>b = %s\n>>>>hd = %s\n"
                               uu____16525 uu____16527 uu____16529)
                          else ();
                          FStar_Pervasives_Native.Some bv)
                     | uu____16534 -> FStar_Pervasives_Native.None))
                in
             let is_applied_maybe_squashed bs t =
               if (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
               then
                 (let uu____16552 = FStar_Syntax_Print.term_to_string t  in
                  let uu____16554 = FStar_Syntax_Print.tag_of_term t  in
                  FStar_Util.print2
                    "WPE> is_applied_maybe_squashed %s -- %s\n" uu____16552
                    uu____16554)
               else ();
               (let uu____16559 = FStar_Syntax_Util.is_squash t  in
                match uu____16559 with
                | FStar_Pervasives_Native.Some (uu____16570,t') ->
                    is_applied bs t'
                | uu____16582 ->
                    let uu____16591 = FStar_Syntax_Util.is_auto_squash t  in
                    (match uu____16591 with
                     | FStar_Pervasives_Native.Some (uu____16602,t') ->
                         is_applied bs t'
                     | uu____16614 -> is_applied bs t))
                in
             let is_quantified_const bv phi =
               let uu____16638 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16638 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
                   (lid,(p,uu____16645)::(q,uu____16647)::[])) when
                   FStar_Ident.lid_equals lid FStar_Parser_Const.imp_lid ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____16690 = FStar_Syntax_Print.term_to_string p
                          in
                       let uu____16692 = FStar_Syntax_Print.term_to_string q
                          in
                       FStar_Util.print2 "WPE> p = (%s); q = (%s)\n"
                         uu____16690 uu____16692)
                    else ();
                    (let uu____16697 =
                       FStar_Syntax_Util.destruct_typ_as_formula p  in
                     match uu____16697 with
                     | FStar_Pervasives_Native.None  ->
                         let uu____16702 =
                           let uu____16703 = FStar_Syntax_Subst.compress p
                              in
                           uu____16703.FStar_Syntax_Syntax.n  in
                         (match uu____16702 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 1\n"
                               else ();
                               (let uu____16714 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_true)] q
                                   in
                                FStar_Pervasives_Native.Some uu____16714))
                          | uu____16717 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some
                         (FStar_Syntax_Util.BaseConn
                         (lid1,(p1,uu____16720)::[])) when
                         FStar_Ident.lid_equals lid1
                           FStar_Parser_Const.not_lid
                         ->
                         let uu____16745 =
                           let uu____16746 = FStar_Syntax_Subst.compress p1
                              in
                           uu____16746.FStar_Syntax_Syntax.n  in
                         (match uu____16745 with
                          | FStar_Syntax_Syntax.Tm_bvar bv' when
                              FStar_Syntax_Syntax.bv_eq bv bv' ->
                              (if
                                 (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                               then FStar_Util.print_string "WPE> Case 2\n"
                               else ();
                               (let uu____16757 =
                                  FStar_Syntax_Subst.subst
                                    [FStar_Syntax_Syntax.NT
                                       (bv, FStar_Syntax_Util.t_false)] q
                                   in
                                FStar_Pervasives_Native.Some uu____16757))
                          | uu____16760 -> FStar_Pervasives_Native.None)
                     | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                         (bs,np,pats,phi1)) ->
                         let uu____16767 =
                           FStar_Syntax_Util.destruct_typ_as_formula phi1  in
                         (match uu____16767 with
                          | FStar_Pervasives_Native.None  ->
                              let uu____16772 =
                                is_applied_maybe_squashed bs phi1  in
                              (match uu____16772 with
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
                                     let uu____16786 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ftrue)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____16786))
                               | uu____16789 -> FStar_Pervasives_Native.None)
                          | FStar_Pervasives_Native.Some
                              (FStar_Syntax_Util.BaseConn
                              (lid1,(p1,uu____16794)::[])) when
                              FStar_Ident.lid_equals lid1
                                FStar_Parser_Const.not_lid
                              ->
                              let uu____16819 =
                                is_applied_maybe_squashed bs p1  in
                              (match uu____16819 with
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
                                     let uu____16833 =
                                       FStar_Syntax_Subst.subst
                                         [FStar_Syntax_Syntax.NT (bv, ffalse)]
                                         q
                                        in
                                     FStar_Pervasives_Native.Some uu____16833))
                               | uu____16836 -> FStar_Pervasives_Native.None)
                          | uu____16839 -> FStar_Pervasives_Native.None)
                     | uu____16842 -> FStar_Pervasives_Native.None))
               | uu____16845 -> FStar_Pervasives_Native.None  in
             let is_forall_const phi =
               let uu____16858 =
                 FStar_Syntax_Util.destruct_typ_as_formula phi  in
               match uu____16858 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
                   ((bv,uu____16864)::[],uu____16865,uu____16866,phi')) ->
                   (if
                      (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                    then
                      (let uu____16888 = FStar_Syntax_Print.bv_to_string bv
                          in
                       let uu____16890 =
                         FStar_Syntax_Print.term_to_string phi'  in
                       FStar_Util.print2 "WPE> QAll [%s] %s\n" uu____16888
                         uu____16890)
                    else ();
                    is_quantified_const bv phi')
               | uu____16895 -> FStar_Pervasives_Native.None  in
             let is_const_match phi =
               let uu____16910 =
                 let uu____16911 = FStar_Syntax_Subst.compress phi  in
                 uu____16911.FStar_Syntax_Syntax.n  in
               match uu____16910 with
               | FStar_Syntax_Syntax.Tm_match (uu____16917,br::brs) ->
                   let uu____16984 = br  in
                   (match uu____16984 with
                    | (uu____17002,uu____17003,e) ->
                        let r =
                          let uu____17025 = simp_t e  in
                          match uu____17025 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some b ->
                              let uu____17037 =
                                FStar_List.for_all
                                  (fun uu____17056  ->
                                     match uu____17056 with
                                     | (uu____17070,uu____17071,e') ->
                                         let uu____17085 = simp_t e'  in
                                         uu____17085 =
                                           (FStar_Pervasives_Native.Some b))
                                  brs
                                 in
                              if uu____17037
                              then FStar_Pervasives_Native.Some b
                              else FStar_Pervasives_Native.None
                           in
                        r)
               | uu____17101 -> FStar_Pervasives_Native.None  in
             let maybe_auto_squash t =
               let uu____17111 = FStar_Syntax_Util.is_sub_singleton t  in
               if uu____17111
               then t
               else
                 FStar_Syntax_Util.mk_auto_squash FStar_Syntax_Syntax.U_zero
                   t
                in
             let squashed_head_un_auto_squash_args t =
               let maybe_un_auto_squash_arg uu____17149 =
                 match uu____17149 with
                 | (t1,q) ->
                     let uu____17170 = FStar_Syntax_Util.is_auto_squash t1
                        in
                     (match uu____17170 with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.U_zero ,t2) -> (t2, q)
                      | uu____17202 -> (t1, q))
                  in
               let uu____17215 = FStar_Syntax_Util.head_and_args t  in
               match uu____17215 with
               | (head1,args) ->
                   let args1 = FStar_List.map maybe_un_auto_squash_arg args
                      in
                   FStar_Syntax_Syntax.mk_Tm_app head1 args1
                     FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                in
             let rec clearly_inhabited ty =
               let uu____17295 =
                 let uu____17296 = FStar_Syntax_Util.unmeta ty  in
                 uu____17296.FStar_Syntax_Syntax.n  in
               match uu____17295 with
               | FStar_Syntax_Syntax.Tm_uinst (t,uu____17301) ->
                   clearly_inhabited t
               | FStar_Syntax_Syntax.Tm_arrow (uu____17306,c) ->
                   clearly_inhabited (FStar_Syntax_Util.comp_result c)
               | FStar_Syntax_Syntax.Tm_fvar fv ->
                   let l = FStar_Syntax_Syntax.lid_of_fv fv  in
                   (((FStar_Ident.lid_equals l FStar_Parser_Const.int_lid) ||
                       (FStar_Ident.lid_equals l FStar_Parser_Const.bool_lid))
                      ||
                      (FStar_Ident.lid_equals l FStar_Parser_Const.string_lid))
                     || (FStar_Ident.lid_equals l FStar_Parser_Const.exn_lid)
               | uu____17330 -> false  in
             let simplify1 arg =
               let uu____17363 = simp_t (FStar_Pervasives_Native.fst arg)  in
               (uu____17363, arg)  in
             let uu____17378 = is_forall_const tm1  in
             match uu____17378 with
             | FStar_Pervasives_Native.Some tm' ->
                 (if
                    (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.wpe
                  then
                    (let uu____17384 = FStar_Syntax_Print.term_to_string tm1
                        in
                     let uu____17386 = FStar_Syntax_Print.term_to_string tm'
                        in
                     FStar_Util.print2 "WPE> %s ~> %s\n" uu____17384
                       uu____17386)
                  else ();
                  (let uu____17391 = norm cfg env [] tm'  in
                   maybe_simplify_aux cfg env stack uu____17391))
             | FStar_Pervasives_Native.None  ->
                 let uu____17392 =
                   let uu____17393 = FStar_Syntax_Subst.compress tm1  in
                   uu____17393.FStar_Syntax_Syntax.n  in
                 (match uu____17392 with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                           ({
                              FStar_Syntax_Syntax.n =
                                FStar_Syntax_Syntax.Tm_fvar fv;
                              FStar_Syntax_Syntax.pos = uu____17397;
                              FStar_Syntax_Syntax.vars = uu____17398;_},uu____17399);
                         FStar_Syntax_Syntax.pos = uu____17400;
                         FStar_Syntax_Syntax.vars = uu____17401;_},args)
                      ->
                      let uu____17431 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____17431
                      then
                        let uu____17434 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____17434 with
                         | (FStar_Pervasives_Native.Some (true ),uu____17492)::
                             (uu____17493,(arg,uu____17495))::[] ->
                             maybe_auto_squash arg
                         | (uu____17568,(arg,uu____17570))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____17571)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____17644)::uu____17645::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____17715::(FStar_Pervasives_Native.Some (false
                                         ),uu____17716)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____17786 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____17804 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____17804
                         then
                           let uu____17807 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____17807 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____17865)::uu____17866::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____17936::(FStar_Pervasives_Native.Some (true
                                           ),uu____17937)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____18007)::(uu____18008,(arg,uu____18010))::[]
                               -> maybe_auto_squash arg
                           | (uu____18083,(arg,uu____18085))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____18086)::[]
                               -> maybe_auto_squash arg
                           | uu____18159 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____18177 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____18177
                            then
                              let uu____18180 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____18180 with
                              | uu____18238::(FStar_Pervasives_Native.Some
                                              (true ),uu____18239)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____18309)::uu____18310::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____18380)::(uu____18381,(arg,uu____18383))::[]
                                  -> maybe_auto_squash arg
                              | (uu____18456,(p,uu____18458))::(uu____18459,
                                                                (q,uu____18461))::[]
                                  ->
                                  let uu____18533 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____18533
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____18538 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____18556 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____18556
                               then
                                 let uu____18559 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____18559 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18617)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18618)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18692)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18693)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18767)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____18768)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____18842)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____18843)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____18917,(arg,uu____18919))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____18920)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____18993)::(uu____18994,(arg,uu____18996))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____19069,(arg,uu____19071))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____19072)::[]
                                     ->
                                     let uu____19145 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19145
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____19146)::(uu____19147,(arg,uu____19149))::[]
                                     ->
                                     let uu____19222 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____19222
                                 | (uu____19223,(p,uu____19225))::(uu____19226,
                                                                   (q,uu____19228))::[]
                                     ->
                                     let uu____19300 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____19300
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____19305 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____19323 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____19323
                                  then
                                    let uu____19326 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____19326 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____19384)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____19428)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____19472 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____19490 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____19490
                                     then
                                       match args with
                                       | (t,uu____19494)::[] ->
                                           let uu____19519 =
                                             let uu____19520 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19520.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19519 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19523::[],body,uu____19525)
                                                ->
                                                let uu____19560 = simp_t body
                                                   in
                                                (match uu____19560 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____19566 -> tm1)
                                            | uu____19570 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____19572))::(t,uu____19574)::[]
                                           ->
                                           let uu____19614 =
                                             let uu____19615 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____19615.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____19614 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____19618::[],body,uu____19620)
                                                ->
                                                let uu____19655 = simp_t body
                                                   in
                                                (match uu____19655 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____19663 -> tm1)
                                            | uu____19667 -> tm1)
                                       | uu____19668 -> tm1
                                     else
                                       (let uu____19681 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____19681
                                        then
                                          match args with
                                          | (t,uu____19685)::[] ->
                                              let uu____19710 =
                                                let uu____19711 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19711.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19710 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19714::[],body,uu____19716)
                                                   ->
                                                   let uu____19751 =
                                                     simp_t body  in
                                                   (match uu____19751 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____19757 -> tm1)
                                               | uu____19761 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____19763))::(t,uu____19765)::[]
                                              ->
                                              let uu____19805 =
                                                let uu____19806 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____19806.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____19805 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____19809::[],body,uu____19811)
                                                   ->
                                                   let uu____19846 =
                                                     simp_t body  in
                                                   (match uu____19846 with
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
                                                    | uu____19854 -> tm1)
                                               | uu____19858 -> tm1)
                                          | uu____19859 -> tm1
                                        else
                                          (let uu____19872 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____19872
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19875;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19876;_},uu____19877)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____19903;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____19904;_},uu____19905)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____19931 -> tm1
                                           else
                                             (let uu____19944 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____19944
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____19958 =
                                                    let uu____19959 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____19959.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____19958 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____19970 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____19984 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____19984
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____20023 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____20023
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____20029 =
                                                         let uu____20030 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____20030.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____20029 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____20033 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____20041 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____20041
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____20050
                                                                  =
                                                                  let uu____20051
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____20051.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____20050
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____20057)
                                                                    -> hd1
                                                                | uu____20082
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____20086
                                                                =
                                                                let uu____20097
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____20097]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____20086)
                                                       | uu____20130 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____20135 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____20135 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____20155 ->
                                                     let uu____20164 =
                                                       let uu____20171 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____20171 cfg env
                                                        in
                                                     uu____20164 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____20177;
                         FStar_Syntax_Syntax.vars = uu____20178;_},args)
                      ->
                      let uu____20204 =
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.and_lid
                         in
                      if uu____20204
                      then
                        let uu____20207 =
                          FStar_All.pipe_right args
                            (FStar_List.map simplify1)
                           in
                        (match uu____20207 with
                         | (FStar_Pervasives_Native.Some (true ),uu____20265)::
                             (uu____20266,(arg,uu____20268))::[] ->
                             maybe_auto_squash arg
                         | (uu____20341,(arg,uu____20343))::(FStar_Pervasives_Native.Some
                                                             (true
                                                             ),uu____20344)::[]
                             -> maybe_auto_squash arg
                         | (FStar_Pervasives_Native.Some (false
                            ),uu____20417)::uu____20418::[] ->
                             w FStar_Syntax_Util.t_false
                         | uu____20488::(FStar_Pervasives_Native.Some (false
                                         ),uu____20489)::[]
                             -> w FStar_Syntax_Util.t_false
                         | uu____20559 ->
                             squashed_head_un_auto_squash_args tm1)
                      else
                        (let uu____20577 =
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.or_lid
                            in
                         if uu____20577
                         then
                           let uu____20580 =
                             FStar_All.pipe_right args
                               (FStar_List.map simplify1)
                              in
                           match uu____20580 with
                           | (FStar_Pervasives_Native.Some (true
                              ),uu____20638)::uu____20639::[] ->
                               w FStar_Syntax_Util.t_true
                           | uu____20709::(FStar_Pervasives_Native.Some (true
                                           ),uu____20710)::[]
                               -> w FStar_Syntax_Util.t_true
                           | (FStar_Pervasives_Native.Some (false
                              ),uu____20780)::(uu____20781,(arg,uu____20783))::[]
                               -> maybe_auto_squash arg
                           | (uu____20856,(arg,uu____20858))::(FStar_Pervasives_Native.Some
                                                               (false
                                                               ),uu____20859)::[]
                               -> maybe_auto_squash arg
                           | uu____20932 ->
                               squashed_head_un_auto_squash_args tm1
                         else
                           (let uu____20950 =
                              FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.imp_lid
                               in
                            if uu____20950
                            then
                              let uu____20953 =
                                FStar_All.pipe_right args
                                  (FStar_List.map simplify1)
                                 in
                              match uu____20953 with
                              | uu____21011::(FStar_Pervasives_Native.Some
                                              (true ),uu____21012)::[]
                                  -> w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (false
                                 ),uu____21082)::uu____21083::[] ->
                                  w FStar_Syntax_Util.t_true
                              | (FStar_Pervasives_Native.Some (true
                                 ),uu____21153)::(uu____21154,(arg,uu____21156))::[]
                                  -> maybe_auto_squash arg
                              | (uu____21229,(p,uu____21231))::(uu____21232,
                                                                (q,uu____21234))::[]
                                  ->
                                  let uu____21306 =
                                    FStar_Syntax_Util.term_eq p q  in
                                  (if uu____21306
                                   then w FStar_Syntax_Util.t_true
                                   else squashed_head_un_auto_squash_args tm1)
                              | uu____21311 ->
                                  squashed_head_un_auto_squash_args tm1
                            else
                              (let uu____21329 =
                                 FStar_Syntax_Syntax.fv_eq_lid fv
                                   FStar_Parser_Const.iff_lid
                                  in
                               if uu____21329
                               then
                                 let uu____21332 =
                                   FStar_All.pipe_right args
                                     (FStar_List.map simplify1)
                                    in
                                 match uu____21332 with
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21390)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21391)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21465)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21466)::[]
                                     -> w FStar_Syntax_Util.t_true
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21540)::(FStar_Pervasives_Native.Some
                                                     (false ),uu____21541)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21615)::(FStar_Pervasives_Native.Some
                                                     (true ),uu____21616)::[]
                                     -> w FStar_Syntax_Util.t_false
                                 | (uu____21690,(arg,uu____21692))::(FStar_Pervasives_Native.Some
                                                                    (true
                                                                    ),uu____21693)::[]
                                     -> maybe_auto_squash arg
                                 | (FStar_Pervasives_Native.Some (true
                                    ),uu____21766)::(uu____21767,(arg,uu____21769))::[]
                                     -> maybe_auto_squash arg
                                 | (uu____21842,(arg,uu____21844))::(FStar_Pervasives_Native.Some
                                                                    (false
                                                                    ),uu____21845)::[]
                                     ->
                                     let uu____21918 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21918
                                 | (FStar_Pervasives_Native.Some (false
                                    ),uu____21919)::(uu____21920,(arg,uu____21922))::[]
                                     ->
                                     let uu____21995 =
                                       FStar_Syntax_Util.mk_neg arg  in
                                     maybe_auto_squash uu____21995
                                 | (uu____21996,(p,uu____21998))::(uu____21999,
                                                                   (q,uu____22001))::[]
                                     ->
                                     let uu____22073 =
                                       FStar_Syntax_Util.term_eq p q  in
                                     (if uu____22073
                                      then w FStar_Syntax_Util.t_true
                                      else
                                        squashed_head_un_auto_squash_args tm1)
                                 | uu____22078 ->
                                     squashed_head_un_auto_squash_args tm1
                               else
                                 (let uu____22096 =
                                    FStar_Syntax_Syntax.fv_eq_lid fv
                                      FStar_Parser_Const.not_lid
                                     in
                                  if uu____22096
                                  then
                                    let uu____22099 =
                                      FStar_All.pipe_right args
                                        (FStar_List.map simplify1)
                                       in
                                    match uu____22099 with
                                    | (FStar_Pervasives_Native.Some (true
                                       ),uu____22157)::[] ->
                                        w FStar_Syntax_Util.t_false
                                    | (FStar_Pervasives_Native.Some (false
                                       ),uu____22201)::[] ->
                                        w FStar_Syntax_Util.t_true
                                    | uu____22245 ->
                                        squashed_head_un_auto_squash_args tm1
                                  else
                                    (let uu____22263 =
                                       FStar_Syntax_Syntax.fv_eq_lid fv
                                         FStar_Parser_Const.forall_lid
                                        in
                                     if uu____22263
                                     then
                                       match args with
                                       | (t,uu____22267)::[] ->
                                           let uu____22292 =
                                             let uu____22293 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22293.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22292 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22296::[],body,uu____22298)
                                                ->
                                                let uu____22333 = simp_t body
                                                   in
                                                (match uu____22333 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | uu____22339 -> tm1)
                                            | uu____22343 -> tm1)
                                       | (ty,FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Implicit
                                          uu____22345))::(t,uu____22347)::[]
                                           ->
                                           let uu____22387 =
                                             let uu____22388 =
                                               FStar_Syntax_Subst.compress t
                                                in
                                             uu____22388.FStar_Syntax_Syntax.n
                                              in
                                           (match uu____22387 with
                                            | FStar_Syntax_Syntax.Tm_abs
                                                (uu____22391::[],body,uu____22393)
                                                ->
                                                let uu____22428 = simp_t body
                                                   in
                                                (match uu____22428 with
                                                 | FStar_Pervasives_Native.Some
                                                     (true ) ->
                                                     w
                                                       FStar_Syntax_Util.t_true
                                                 | FStar_Pervasives_Native.Some
                                                     (false ) when
                                                     clearly_inhabited ty ->
                                                     w
                                                       FStar_Syntax_Util.t_false
                                                 | uu____22436 -> tm1)
                                            | uu____22440 -> tm1)
                                       | uu____22441 -> tm1
                                     else
                                       (let uu____22454 =
                                          FStar_Syntax_Syntax.fv_eq_lid fv
                                            FStar_Parser_Const.exists_lid
                                           in
                                        if uu____22454
                                        then
                                          match args with
                                          | (t,uu____22458)::[] ->
                                              let uu____22483 =
                                                let uu____22484 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22484.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22483 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22487::[],body,uu____22489)
                                                   ->
                                                   let uu____22524 =
                                                     simp_t body  in
                                                   (match uu____22524 with
                                                    | FStar_Pervasives_Native.Some
                                                        (false ) ->
                                                        w
                                                          FStar_Syntax_Util.t_false
                                                    | uu____22530 -> tm1)
                                               | uu____22534 -> tm1)
                                          | (ty,FStar_Pervasives_Native.Some
                                             (FStar_Syntax_Syntax.Implicit
                                             uu____22536))::(t,uu____22538)::[]
                                              ->
                                              let uu____22578 =
                                                let uu____22579 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____22579.FStar_Syntax_Syntax.n
                                                 in
                                              (match uu____22578 with
                                               | FStar_Syntax_Syntax.Tm_abs
                                                   (uu____22582::[],body,uu____22584)
                                                   ->
                                                   let uu____22619 =
                                                     simp_t body  in
                                                   (match uu____22619 with
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
                                                    | uu____22627 -> tm1)
                                               | uu____22631 -> tm1)
                                          | uu____22632 -> tm1
                                        else
                                          (let uu____22645 =
                                             FStar_Syntax_Syntax.fv_eq_lid fv
                                               FStar_Parser_Const.b2t_lid
                                              in
                                           if uu____22645
                                           then
                                             match args with
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (true ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22648;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22649;_},uu____22650)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_true
                                             | ({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_constant
                                                    (FStar_Const.Const_bool
                                                    (false ));
                                                  FStar_Syntax_Syntax.pos =
                                                    uu____22676;
                                                  FStar_Syntax_Syntax.vars =
                                                    uu____22677;_},uu____22678)::[]
                                                 ->
                                                 w FStar_Syntax_Util.t_false
                                             | uu____22704 -> tm1
                                           else
                                             (let uu____22717 =
                                                FStar_Syntax_Syntax.fv_eq_lid
                                                  fv
                                                  FStar_Parser_Const.haseq_lid
                                                 in
                                              if uu____22717
                                              then
                                                let t_has_eq_for_sure t =
                                                  let haseq_lids =
                                                    [FStar_Parser_Const.int_lid;
                                                    FStar_Parser_Const.bool_lid;
                                                    FStar_Parser_Const.unit_lid;
                                                    FStar_Parser_Const.string_lid]
                                                     in
                                                  let uu____22731 =
                                                    let uu____22732 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____22732.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____22731 with
                                                  | FStar_Syntax_Syntax.Tm_fvar
                                                      fv1 when
                                                      FStar_All.pipe_right
                                                        haseq_lids
                                                        (FStar_List.existsb
                                                           (fun l  ->
                                                              FStar_Syntax_Syntax.fv_eq_lid
                                                                fv1 l))
                                                      -> true
                                                  | uu____22743 -> false  in
                                                (if
                                                   (FStar_List.length args) =
                                                     (Prims.parse_int "1")
                                                 then
                                                   let t =
                                                     let uu____22757 =
                                                       FStar_All.pipe_right
                                                         args FStar_List.hd
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____22757
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____22792 =
                                                     FStar_All.pipe_right t
                                                       t_has_eq_for_sure
                                                      in
                                                   (if uu____22792
                                                    then
                                                      w
                                                        FStar_Syntax_Util.t_true
                                                    else
                                                      (let uu____22798 =
                                                         let uu____22799 =
                                                           FStar_Syntax_Subst.compress
                                                             t
                                                            in
                                                         uu____22799.FStar_Syntax_Syntax.n
                                                          in
                                                       match uu____22798 with
                                                       | FStar_Syntax_Syntax.Tm_refine
                                                           uu____22802 ->
                                                           let t1 =
                                                             FStar_Syntax_Util.unrefine
                                                               t
                                                              in
                                                           let uu____22810 =
                                                             FStar_All.pipe_right
                                                               t1
                                                               t_has_eq_for_sure
                                                              in
                                                           if uu____22810
                                                           then
                                                             w
                                                               FStar_Syntax_Util.t_true
                                                           else
                                                             (let haseq_tm =
                                                                let uu____22819
                                                                  =
                                                                  let uu____22820
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    tm1  in
                                                                  uu____22820.FStar_Syntax_Syntax.n
                                                                   in
                                                                match uu____22819
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_app
                                                                    (hd1,uu____22826)
                                                                    -> hd1
                                                                | uu____22851
                                                                    ->
                                                                    failwith
                                                                    "Impossible! We have already checked that this is a Tm_app"
                                                                 in
                                                              let uu____22855
                                                                =
                                                                let uu____22866
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____22866]
                                                                 in
                                                              FStar_Syntax_Util.mk_app
                                                                haseq_tm
                                                                uu____22855)
                                                       | uu____22899 -> tm1))
                                                 else tm1)
                                              else
                                                (let uu____22904 =
                                                   FStar_Syntax_Util.is_auto_squash
                                                     tm1
                                                    in
                                                 match uu____22904 with
                                                 | FStar_Pervasives_Native.Some
                                                     (FStar_Syntax_Syntax.U_zero
                                                      ,t)
                                                     when
                                                     FStar_Syntax_Util.is_sub_singleton
                                                       t
                                                     -> t
                                                 | uu____22924 ->
                                                     let uu____22933 =
                                                       let uu____22940 =
                                                         norm_cb cfg  in
                                                       reduce_equality
                                                         uu____22940 cfg env
                                                        in
                                                     uu____22933 tm1)))))))))
                  | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
                      let uu____22951 = simp_t t  in
                      (match uu____22951 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           bv.FStar_Syntax_Syntax.sort
                       | FStar_Pervasives_Native.Some (false ) -> tm1
                       | FStar_Pervasives_Native.None  -> tm1)
                  | FStar_Syntax_Syntax.Tm_match uu____22960 ->
                      let uu____22983 = is_const_match tm1  in
                      (match uu____22983 with
                       | FStar_Pervasives_Native.Some (true ) ->
                           w FStar_Syntax_Util.t_true
                       | FStar_Pervasives_Native.Some (false ) ->
                           w FStar_Syntax_Util.t_false
                       | FStar_Pervasives_Native.None  -> tm1)
                  | uu____22992 -> tm1))

and (rebuild :
  FStar_TypeChecker_Cfg.cfg ->
    env -> stack -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun cfg  ->
    fun env  ->
      fun stack  ->
        fun t  ->
          FStar_TypeChecker_Cfg.log cfg
            (fun uu____23002  ->
               (let uu____23004 = FStar_Syntax_Print.tag_of_term t  in
                let uu____23006 = FStar_Syntax_Print.term_to_string t  in
                let uu____23008 =
                  FStar_Util.string_of_int (FStar_List.length env)  in
                let uu____23016 =
                  let uu____23018 =
                    let uu____23021 = firstn (Prims.parse_int "4") stack  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____23021
                     in
                  stack_to_string uu____23018  in
                FStar_Util.print4
                  ">>> %s\nRebuild %s with %s env elements and top of the stack %s \n"
                  uu____23004 uu____23006 uu____23008 uu____23016);
               (let uu____23046 =
                  FStar_TypeChecker_Env.debug cfg.FStar_TypeChecker_Cfg.tcenv
                    (FStar_Options.Other "NormRebuild")
                   in
                if uu____23046
                then
                  let uu____23050 = FStar_Syntax_Util.unbound_variables t  in
                  match uu____23050 with
                  | [] -> ()
                  | bvs ->
                      ((let uu____23057 = FStar_Syntax_Print.tag_of_term t
                           in
                        let uu____23059 = FStar_Syntax_Print.term_to_string t
                           in
                        let uu____23061 =
                          let uu____23063 =
                            FStar_All.pipe_right bvs
                              (FStar_List.map FStar_Syntax_Print.bv_to_string)
                             in
                          FStar_All.pipe_right uu____23063
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print3
                          "!!! Rebuild (%s) %s, free vars=%s\n" uu____23057
                          uu____23059 uu____23061);
                       failwith "DIE!")
                else ()));
          (let f_opt = is_fext_on_domain t  in
           let uu____23085 =
             (FStar_All.pipe_right f_opt FStar_Util.is_some) &&
               (match stack with
                | (Arg uu____23093)::uu____23094 -> true
                | uu____23104 -> false)
              in
           if uu____23085
           then
             let uu____23107 = FStar_All.pipe_right f_opt FStar_Util.must  in
             FStar_All.pipe_right uu____23107 (norm cfg env stack)
           else
             (let t1 = maybe_simplify cfg env stack t  in
              match stack with
              | [] -> t1
              | (Debug (tm,time_then))::stack1 ->
                  (if
                     (cfg.FStar_TypeChecker_Cfg.debug).FStar_TypeChecker_Cfg.print_normalized
                   then
                     (let time_now = FStar_Util.now ()  in
                      let uu____23121 =
                        let uu____23123 =
                          let uu____23125 =
                            FStar_Util.time_diff time_then time_now  in
                          FStar_Pervasives_Native.snd uu____23125  in
                        FStar_Util.string_of_int uu____23123  in
                      let uu____23132 = FStar_Syntax_Print.term_to_string tm
                         in
                      let uu____23134 = FStar_Syntax_Print.term_to_string t1
                         in
                      FStar_Util.print3
                        "Normalized term (%s ms) %s\n\tto term %s\n"
                        uu____23121 uu____23132 uu____23134)
                   else ();
                   rebuild cfg env stack1 t1)
              | (Cfg cfg1)::stack1 -> rebuild cfg1 env stack1 t1
              | (Meta (uu____23143,m,r))::stack1 ->
                  let t2 = mk (FStar_Syntax_Syntax.Tm_meta (t1, m)) r  in
                  rebuild cfg env stack1 t2
              | (MemoLazy r)::stack1 ->
                  (set_memo cfg r (env, t1);
                   FStar_TypeChecker_Cfg.log cfg
                     (fun uu____23172  ->
                        let uu____23173 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1 "\tSet memo %s\n" uu____23173);
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
                  let uu____23216 =
                    let uu___2751_23217 = FStar_Syntax_Util.abs bs1 t1 lopt1
                       in
                    {
                      FStar_Syntax_Syntax.n =
                        (uu___2751_23217.FStar_Syntax_Syntax.n);
                      FStar_Syntax_Syntax.pos = r;
                      FStar_Syntax_Syntax.vars =
                        (uu___2751_23217.FStar_Syntax_Syntax.vars)
                    }  in
                  rebuild cfg env stack1 uu____23216
              | (Arg (Univ uu____23220,uu____23221,uu____23222))::uu____23223
                  -> failwith "Impossible"
              | (Arg (Dummy ,uu____23227,uu____23228))::uu____23229 ->
                  failwith "Impossible"
              | (UnivArgs (us,r))::stack1 ->
                  let t2 = FStar_Syntax_Syntax.mk_Tm_uinst t1 us  in
                  rebuild cfg env stack1 t2
              | (Arg
                  (Clos (env_arg,tm,uu____23245,uu____23246),aq,r))::stack1
                  when
                  let uu____23298 = head_of t1  in
                  FStar_Syntax_Util.is_fstar_tactics_by_tactic uu____23298 ->
                  let t2 =
                    let uu____23302 =
                      let uu____23307 =
                        let uu____23308 = closure_as_term cfg env_arg tm  in
                        (uu____23308, aq)  in
                      FStar_Syntax_Syntax.extend_app t1 uu____23307  in
                    uu____23302 FStar_Pervasives_Native.None r  in
                  rebuild cfg env stack1 t2
              | (Arg (Clos (env_arg,tm,m,uu____23318),aq,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg
                     (fun uu____23373  ->
                        let uu____23374 =
                          FStar_Syntax_Print.term_to_string tm  in
                        FStar_Util.print1 "Rebuilding with arg %s\n"
                          uu____23374);
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
                     (let uu____23394 = FStar_ST.op_Bang m  in
                      match uu____23394 with
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
                      | FStar_Pervasives_Native.Some (uu____23482,a) ->
                          let t2 =
                            FStar_Syntax_Syntax.extend_app t1 (a, aq)
                              FStar_Pervasives_Native.None r
                             in
                          rebuild cfg env_arg stack1 t2))
              | (App (env1,head1,aq,r))::stack' when should_reify cfg stack
                  ->
                  let t0 = t1  in
                  let fallback msg uu____23538 =
                    FStar_TypeChecker_Cfg.log cfg
                      (fun uu____23543  ->
                         let uu____23544 =
                           FStar_Syntax_Print.term_to_string t1  in
                         FStar_Util.print2 "Not reifying%s: %s\n" msg
                           uu____23544);
                    (let t2 =
                       FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                         FStar_Pervasives_Native.None r
                        in
                     rebuild cfg env1 stack' t2)
                     in
                  let uu____23554 =
                    let uu____23555 = FStar_Syntax_Subst.compress t1  in
                    uu____23555.FStar_Syntax_Syntax.n  in
                  (match uu____23554 with
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic (m,ty)) ->
                       do_reify_monadic (fallback " (1)") cfg env1 stack t2 m
                         ty
                   | FStar_Syntax_Syntax.Tm_meta
                       (t2,FStar_Syntax_Syntax.Meta_monadic_lift
                        (msrc,mtgt,ty))
                       ->
                       let lifted =
                         let uu____23583 = closure_as_term cfg env1 ty  in
                         reify_lift cfg t2 msrc mtgt uu____23583  in
                       (FStar_TypeChecker_Cfg.log cfg
                          (fun uu____23587  ->
                             let uu____23588 =
                               FStar_Syntax_Print.term_to_string lifted  in
                             FStar_Util.print1 "Reified lift to (1): %s\n"
                               uu____23588);
                        (let uu____23591 = FStar_List.tl stack  in
                         norm cfg env1 uu____23591 lifted))
                   | FStar_Syntax_Syntax.Tm_app
                       ({
                          FStar_Syntax_Syntax.n =
                            FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_reflect uu____23592);
                          FStar_Syntax_Syntax.pos = uu____23593;
                          FStar_Syntax_Syntax.vars = uu____23594;_},(e,uu____23596)::[])
                       -> norm cfg env1 stack' e
                   | FStar_Syntax_Syntax.Tm_app uu____23635 when
                       (cfg.FStar_TypeChecker_Cfg.steps).FStar_TypeChecker_Cfg.primops
                       ->
                       let uu____23652 = FStar_Syntax_Util.head_and_args t1
                          in
                       (match uu____23652 with
                        | (hd1,args) ->
                            let uu____23695 =
                              let uu____23696 =
                                FStar_Syntax_Util.un_uinst hd1  in
                              uu____23696.FStar_Syntax_Syntax.n  in
                            (match uu____23695 with
                             | FStar_Syntax_Syntax.Tm_fvar fv ->
                                 let uu____23700 =
                                   FStar_TypeChecker_Cfg.find_prim_step cfg
                                     fv
                                    in
                                 (match uu____23700 with
                                  | FStar_Pervasives_Native.Some
                                      {
                                        FStar_TypeChecker_Cfg.name =
                                          uu____23703;
                                        FStar_TypeChecker_Cfg.arity =
                                          uu____23704;
                                        FStar_TypeChecker_Cfg.univ_arity =
                                          uu____23705;
                                        FStar_TypeChecker_Cfg.auto_reflect =
                                          FStar_Pervasives_Native.Some n1;
                                        FStar_TypeChecker_Cfg.strong_reduction_ok
                                          = uu____23707;
                                        FStar_TypeChecker_Cfg.requires_binder_substitution
                                          = uu____23708;
                                        FStar_TypeChecker_Cfg.interpretation
                                          = uu____23709;
                                        FStar_TypeChecker_Cfg.interpretation_nbe
                                          = uu____23710;_}
                                      when (FStar_List.length args) = n1 ->
                                      norm cfg env1 stack' t1
                                  | uu____23746 -> fallback " (3)" ())
                             | uu____23750 -> fallback " (4)" ()))
                   | uu____23752 -> fallback " (2)" ())
              | (App (env1,head1,aq,r))::stack1 ->
                  let t2 =
                    FStar_Syntax_Syntax.extend_app head1 (t1, aq)
                      FStar_Pervasives_Native.None r
                     in
                  rebuild cfg env1 stack1 t2
              | (Match (env',branches,cfg1,r))::stack1 ->
                  (FStar_TypeChecker_Cfg.log cfg1
                     (fun uu____23778  ->
                        let uu____23779 =
                          FStar_Syntax_Print.term_to_string t1  in
                        FStar_Util.print1
                          "Rebuilding with match, scrutinee is %s ...\n"
                          uu____23779);
                   (let scrutinee_env = env  in
                    let env1 = env'  in
                    let scrutinee = t1  in
                    let norm_and_rebuild_match uu____23790 =
                      FStar_TypeChecker_Cfg.log cfg1
                        (fun uu____23795  ->
                           let uu____23796 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           let uu____23798 =
                             let uu____23800 =
                               FStar_All.pipe_right branches
                                 (FStar_List.map
                                    (fun uu____23830  ->
                                       match uu____23830 with
                                       | (p,uu____23841,uu____23842) ->
                                           FStar_Syntax_Print.pat_to_string p))
                                in
                             FStar_All.pipe_right uu____23800
                               (FStar_String.concat "\n\t")
                              in
                           FStar_Util.print2
                             "match is irreducible: scrutinee=%s\nbranches=%s\n"
                             uu____23796 uu____23798);
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
                                (fun uu___17_23864  ->
                                   match uu___17_23864 with
                                   | FStar_TypeChecker_Env.InliningDelta  ->
                                       true
                                   | FStar_TypeChecker_Env.Eager_unfolding_only
                                        -> true
                                   | uu____23868 -> false))
                            in
                         let steps =
                           let uu___2919_23871 =
                             cfg1.FStar_TypeChecker_Cfg.steps  in
                           {
                             FStar_TypeChecker_Cfg.beta =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.beta);
                             FStar_TypeChecker_Cfg.iota =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.iota);
                             FStar_TypeChecker_Cfg.zeta = false;
                             FStar_TypeChecker_Cfg.weak =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.weak);
                             FStar_TypeChecker_Cfg.hnf =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.hnf);
                             FStar_TypeChecker_Cfg.primops =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.primops);
                             FStar_TypeChecker_Cfg.do_not_unfold_pure_lets =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                             FStar_TypeChecker_Cfg.unfold_until =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_only =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_fully =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.unfold_fully);
                             FStar_TypeChecker_Cfg.unfold_attr =
                               FStar_Pervasives_Native.None;
                             FStar_TypeChecker_Cfg.unfold_tac = false;
                             FStar_TypeChecker_Cfg.pure_subterms_within_computations
                               =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                             FStar_TypeChecker_Cfg.simplify =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.simplify);
                             FStar_TypeChecker_Cfg.erase_universes =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.erase_universes);
                             FStar_TypeChecker_Cfg.allow_unbound_universes =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.allow_unbound_universes);
                             FStar_TypeChecker_Cfg.reify_ =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.reify_);
                             FStar_TypeChecker_Cfg.compress_uvars =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.compress_uvars);
                             FStar_TypeChecker_Cfg.no_full_norm =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.no_full_norm);
                             FStar_TypeChecker_Cfg.check_no_uvars =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.check_no_uvars);
                             FStar_TypeChecker_Cfg.unmeta =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.unmeta);
                             FStar_TypeChecker_Cfg.unascribe =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.unascribe);
                             FStar_TypeChecker_Cfg.in_full_norm_request =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.in_full_norm_request);
                             FStar_TypeChecker_Cfg.weakly_reduce_scrutinee =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.weakly_reduce_scrutinee);
                             FStar_TypeChecker_Cfg.nbe_step =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.nbe_step);
                             FStar_TypeChecker_Cfg.for_extraction =
                               (uu___2919_23871.FStar_TypeChecker_Cfg.for_extraction)
                           }  in
                         let uu___2922_23878 = cfg1  in
                         {
                           FStar_TypeChecker_Cfg.steps = steps;
                           FStar_TypeChecker_Cfg.tcenv =
                             (uu___2922_23878.FStar_TypeChecker_Cfg.tcenv);
                           FStar_TypeChecker_Cfg.debug =
                             (uu___2922_23878.FStar_TypeChecker_Cfg.debug);
                           FStar_TypeChecker_Cfg.delta_level = new_delta;
                           FStar_TypeChecker_Cfg.primitive_steps =
                             (uu___2922_23878.FStar_TypeChecker_Cfg.primitive_steps);
                           FStar_TypeChecker_Cfg.strong = true;
                           FStar_TypeChecker_Cfg.memoize_lazy =
                             (uu___2922_23878.FStar_TypeChecker_Cfg.memoize_lazy);
                           FStar_TypeChecker_Cfg.normalize_pure_lets =
                             (uu___2922_23878.FStar_TypeChecker_Cfg.normalize_pure_lets);
                           FStar_TypeChecker_Cfg.reifying =
                             (uu___2922_23878.FStar_TypeChecker_Cfg.reifying)
                         }  in
                       let norm_or_whnf env2 t2 =
                         if whnf
                         then closure_as_term cfg_exclude_zeta env2 t2
                         else norm cfg_exclude_zeta env2 [] t2  in
                       let rec norm_pat env2 p =
                         match p.FStar_Syntax_Syntax.v with
                         | FStar_Syntax_Syntax.Pat_constant uu____23953 ->
                             (p, env2)
                         | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
                             let uu____23984 =
                               FStar_All.pipe_right pats
                                 (FStar_List.fold_left
                                    (fun uu____24073  ->
                                       fun uu____24074  ->
                                         match (uu____24073, uu____24074)
                                         with
                                         | ((pats1,env3),(p1,b)) ->
                                             let uu____24224 =
                                               norm_pat env3 p1  in
                                             (match uu____24224 with
                                              | (p2,env4) ->
                                                  (((p2, b) :: pats1), env4)))
                                    ([], env2))
                                in
                             (match uu____23984 with
                              | (pats1,env3) ->
                                  ((let uu___2950_24394 = p  in
                                    {
                                      FStar_Syntax_Syntax.v =
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, (FStar_List.rev pats1)));
                                      FStar_Syntax_Syntax.p =
                                        (uu___2950_24394.FStar_Syntax_Syntax.p)
                                    }), env3))
                         | FStar_Syntax_Syntax.Pat_var x ->
                             let x1 =
                               let uu___2954_24415 = x  in
                               let uu____24416 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2954_24415.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2954_24415.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24416
                               }  in
                             ((let uu___2957_24430 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_var x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___2957_24430.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_wild x ->
                             let x1 =
                               let uu___2961_24441 = x  in
                               let uu____24442 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2961_24441.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2961_24441.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24442
                               }  in
                             ((let uu___2964_24456 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_wild x1);
                                 FStar_Syntax_Syntax.p =
                                   (uu___2964_24456.FStar_Syntax_Syntax.p)
                               }), (dummy :: env2))
                         | FStar_Syntax_Syntax.Pat_dot_term (x,t2) ->
                             let x1 =
                               let uu___2970_24472 = x  in
                               let uu____24473 =
                                 norm_or_whnf env2 x.FStar_Syntax_Syntax.sort
                                  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2970_24472.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2970_24472.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = uu____24473
                               }  in
                             let t3 = norm_or_whnf env2 t2  in
                             ((let uu___2974_24488 = p  in
                               {
                                 FStar_Syntax_Syntax.v =
                                   (FStar_Syntax_Syntax.Pat_dot_term (x1, t3));
                                 FStar_Syntax_Syntax.p =
                                   (uu___2974_24488.FStar_Syntax_Syntax.p)
                               }), env2)
                          in
                       let branches1 =
                         match env1 with
                         | [] when whnf -> branches
                         | uu____24532 ->
                             FStar_All.pipe_right branches
                               (FStar_List.map
                                  (fun branch1  ->
                                     let uu____24562 =
                                       FStar_Syntax_Subst.open_branch branch1
                                        in
                                     match uu____24562 with
                                     | (p,wopt,e) ->
                                         let uu____24582 = norm_pat env1 p
                                            in
                                         (match uu____24582 with
                                          | (p1,env2) ->
                                              let wopt1 =
                                                match wopt with
                                                | FStar_Pervasives_Native.None
                                                     ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    w ->
                                                    let uu____24637 =
                                                      norm_or_whnf env2 w  in
                                                    FStar_Pervasives_Native.Some
                                                      uu____24637
                                                 in
                                              let e1 = norm_or_whnf env2 e
                                                 in
                                              FStar_Syntax_Util.branch
                                                (p1, wopt1, e1))))
                          in
                       let scrutinee1 =
                         let uu____24654 =
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
                         if uu____24654
                         then
                           norm
                             (let uu___2993_24661 = cfg1  in
                              {
                                FStar_TypeChecker_Cfg.steps =
                                  (let uu___2995_24664 =
                                     cfg1.FStar_TypeChecker_Cfg.steps  in
                                   {
                                     FStar_TypeChecker_Cfg.beta =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.beta);
                                     FStar_TypeChecker_Cfg.iota =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.iota);
                                     FStar_TypeChecker_Cfg.zeta =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.zeta);
                                     FStar_TypeChecker_Cfg.weak =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.weak);
                                     FStar_TypeChecker_Cfg.hnf =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.hnf);
                                     FStar_TypeChecker_Cfg.primops =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.primops);
                                     FStar_TypeChecker_Cfg.do_not_unfold_pure_lets
                                       =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.do_not_unfold_pure_lets);
                                     FStar_TypeChecker_Cfg.unfold_until =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.unfold_until);
                                     FStar_TypeChecker_Cfg.unfold_only =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.unfold_only);
                                     FStar_TypeChecker_Cfg.unfold_fully =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.unfold_fully);
                                     FStar_TypeChecker_Cfg.unfold_attr =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.unfold_attr);
                                     FStar_TypeChecker_Cfg.unfold_tac =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.unfold_tac);
                                     FStar_TypeChecker_Cfg.pure_subterms_within_computations
                                       =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.pure_subterms_within_computations);
                                     FStar_TypeChecker_Cfg.simplify =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.simplify);
                                     FStar_TypeChecker_Cfg.erase_universes =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.erase_universes);
                                     FStar_TypeChecker_Cfg.allow_unbound_universes
                                       =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.allow_unbound_universes);
                                     FStar_TypeChecker_Cfg.reify_ =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.reify_);
                                     FStar_TypeChecker_Cfg.compress_uvars =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.compress_uvars);
                                     FStar_TypeChecker_Cfg.no_full_norm =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.no_full_norm);
                                     FStar_TypeChecker_Cfg.check_no_uvars =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.check_no_uvars);
                                     FStar_TypeChecker_Cfg.unmeta =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.unmeta);
                                     FStar_TypeChecker_Cfg.unascribe =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.unascribe);
                                     FStar_TypeChecker_Cfg.in_full_norm_request
                                       =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.in_full_norm_request);
                                     FStar_TypeChecker_Cfg.weakly_reduce_scrutinee
                                       = false;
                                     FStar_TypeChecker_Cfg.nbe_step =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.nbe_step);
                                     FStar_TypeChecker_Cfg.for_extraction =
                                       (uu___2995_24664.FStar_TypeChecker_Cfg.for_extraction)
                                   });
                                FStar_TypeChecker_Cfg.tcenv =
                                  (uu___2993_24661.FStar_TypeChecker_Cfg.tcenv);
                                FStar_TypeChecker_Cfg.debug =
                                  (uu___2993_24661.FStar_TypeChecker_Cfg.debug);
                                FStar_TypeChecker_Cfg.delta_level =
                                  (uu___2993_24661.FStar_TypeChecker_Cfg.delta_level);
                                FStar_TypeChecker_Cfg.primitive_steps =
                                  (uu___2993_24661.FStar_TypeChecker_Cfg.primitive_steps);
                                FStar_TypeChecker_Cfg.strong =
                                  (uu___2993_24661.FStar_TypeChecker_Cfg.strong);
                                FStar_TypeChecker_Cfg.memoize_lazy =
                                  (uu___2993_24661.FStar_TypeChecker_Cfg.memoize_lazy);
                                FStar_TypeChecker_Cfg.normalize_pure_lets =
                                  (uu___2993_24661.FStar_TypeChecker_Cfg.normalize_pure_lets);
                                FStar_TypeChecker_Cfg.reifying =
                                  (uu___2993_24661.FStar_TypeChecker_Cfg.reifying)
                              }) scrutinee_env [] scrutinee
                         else scrutinee  in
                       let uu____24668 =
                         mk
                           (FStar_Syntax_Syntax.Tm_match
                              (scrutinee1, branches1)) r
                          in
                       rebuild cfg1 env1 stack1 uu____24668)
                       in
                    let rec is_cons head1 =
                      let uu____24694 =
                        let uu____24695 = FStar_Syntax_Subst.compress head1
                           in
                        uu____24695.FStar_Syntax_Syntax.n  in
                      match uu____24694 with
                      | FStar_Syntax_Syntax.Tm_uinst (h,uu____24700) ->
                          is_cons h
                      | FStar_Syntax_Syntax.Tm_constant uu____24705 -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____24707;
                            FStar_Syntax_Syntax.fv_delta = uu____24708;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Data_ctor );_}
                          -> true
                      | FStar_Syntax_Syntax.Tm_fvar
                          { FStar_Syntax_Syntax.fv_name = uu____24710;
                            FStar_Syntax_Syntax.fv_delta = uu____24711;
                            FStar_Syntax_Syntax.fv_qual =
                              FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor uu____24712);_}
                          -> true
                      | uu____24720 -> false  in
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
                      let uu____24889 =
                        FStar_Syntax_Util.head_and_args scrutinee2  in
                      match uu____24889 with
                      | (head1,args) ->
                          (match p.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_wild bv ->
                               FStar_Util.Inl [(bv, scrutinee_orig)]
                           | FStar_Syntax_Syntax.Pat_dot_term uu____24986 ->
                               FStar_Util.Inl []
                           | FStar_Syntax_Syntax.Pat_constant s ->
                               (match scrutinee2.FStar_Syntax_Syntax.n with
                                | FStar_Syntax_Syntax.Tm_constant s' when
                                    FStar_Const.eq_const s s' ->
                                    FStar_Util.Inl []
                                | uu____25028 ->
                                    let uu____25029 =
                                      let uu____25031 = is_cons head1  in
                                      Prims.op_Negation uu____25031  in
                                    FStar_Util.Inr uu____25029)
                           | FStar_Syntax_Syntax.Pat_cons (fv,arg_pats) ->
                               let uu____25060 =
                                 let uu____25061 =
                                   FStar_Syntax_Util.un_uinst head1  in
                                 uu____25061.FStar_Syntax_Syntax.n  in
                               (match uu____25060 with
                                | FStar_Syntax_Syntax.Tm_fvar fv' when
                                    FStar_Syntax_Syntax.fv_eq fv fv' ->
                                    matches_args [] args arg_pats
                                | uu____25080 ->
                                    let uu____25081 =
                                      let uu____25083 = is_cons head1  in
                                      Prims.op_Negation uu____25083  in
                                    FStar_Util.Inr uu____25081))
                    
                    and matches_args out a p =
                      match (a, p) with
                      | ([],[]) -> FStar_Util.Inl out
                      | ((t2,uu____25174)::rest_a,(p1,uu____25177)::rest_p)
                          ->
                          let uu____25236 = matches_pat t2 p1  in
                          (match uu____25236 with
                           | FStar_Util.Inl s ->
                               matches_args (FStar_List.append out s) rest_a
                                 rest_p
                           | m -> m)
                      | uu____25289 -> FStar_Util.Inr false
                     in
                    let rec matches scrutinee1 p =
                      match p with
                      | [] -> norm_and_rebuild_match ()
                      | (p1,wopt,b)::rest ->
                          let uu____25412 = matches_pat scrutinee1 p1  in
                          (match uu____25412 with
                           | FStar_Util.Inr (false ) ->
                               matches scrutinee1 rest
                           | FStar_Util.Inr (true ) ->
                               norm_and_rebuild_match ()
                           | FStar_Util.Inl s ->
                               (FStar_TypeChecker_Cfg.log cfg1
                                  (fun uu____25458  ->
                                     let uu____25459 =
                                       FStar_Syntax_Print.pat_to_string p1
                                        in
                                     let uu____25461 =
                                       let uu____25463 =
                                         FStar_List.map
                                           (fun uu____25475  ->
                                              match uu____25475 with
                                              | (uu____25481,t2) ->
                                                  FStar_Syntax_Print.term_to_string
                                                    t2) s
                                          in
                                       FStar_All.pipe_right uu____25463
                                         (FStar_String.concat "; ")
                                        in
                                     FStar_Util.print2
                                       "Matches pattern %s with subst = %s\n"
                                       uu____25459 uu____25461);
                                (let env0 = env1  in
                                 let env2 =
                                   FStar_List.fold_left
                                     (fun env2  ->
                                        fun uu____25517  ->
                                          match uu____25517 with
                                          | (bv,t2) ->
                                              let uu____25540 =
                                                let uu____25547 =
                                                  let uu____25550 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      bv
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____25550
                                                   in
                                                let uu____25551 =
                                                  let uu____25552 =
                                                    let uu____25584 =
                                                      FStar_Util.mk_ref
                                                        (FStar_Pervasives_Native.Some
                                                           ([], t2))
                                                       in
                                                    ([], t2, uu____25584,
                                                      false)
                                                     in
                                                  Clos uu____25552  in
                                                (uu____25547, uu____25551)
                                                 in
                                              uu____25540 :: env2) env1 s
                                    in
                                 let uu____25677 =
                                   guard_when_clause wopt b rest  in
                                 norm cfg1 env2 stack1 uu____25677)))
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
            (fun uu____25710  ->
               let uu____25711 = FStar_TypeChecker_Cfg.cfg_to_string c  in
               FStar_Util.print1 "Cfg = %s\n" uu____25711);
          (let uu____25714 = is_nbe_request s  in
           if uu____25714
           then
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____25720  ->
                   let uu____25721 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting NBE for (%s) {\n" uu____25721);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____25727  ->
                   let uu____25728 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____25728);
              (let uu____25731 =
                 FStar_Util.record_time (fun uu____25738  -> nbe_eval c s t)
                  in
               match uu____25731 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____25747  ->
                         let uu____25748 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____25750 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____25748 uu____25750);
                    r)))
           else
             (FStar_TypeChecker_Cfg.log_top c
                (fun uu____25758  ->
                   let uu____25759 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print1 "Starting normalizer for (%s) {\n"
                     uu____25759);
              FStar_TypeChecker_Cfg.log_top c
                (fun uu____25765  ->
                   let uu____25766 = FStar_TypeChecker_Cfg.cfg_to_string c
                      in
                   FStar_Util.print1 ">>> cfg = %s\n" uu____25766);
              (let uu____25769 =
                 FStar_Util.record_time (fun uu____25776  -> norm c [] [] t)
                  in
               match uu____25769 with
               | (r,ms) ->
                   (FStar_TypeChecker_Cfg.log_top c
                      (fun uu____25791  ->
                         let uu____25792 =
                           FStar_Syntax_Print.term_to_string r  in
                         let uu____25794 = FStar_Util.string_of_int ms  in
                         FStar_Util.print2
                           "}\nNormalization result = (%s) in %s ms\n"
                           uu____25792 uu____25794);
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
        let uu____25829 = FStar_TypeChecker_Cfg.config s e  in
        norm_comp uu____25829 [] t
  
let (normalize_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let uu____25847 = FStar_TypeChecker_Cfg.config [] env  in
      norm_universe uu____25847 [] u
  
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
        let uu____25873 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25873  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____25880 -> c
      | FStar_Syntax_Syntax.GTotal (t,uopt) when non_info t ->
          let uu___3151_25899 = c  in
          {
            FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Total (t, uopt));
            FStar_Syntax_Syntax.pos =
              (uu___3151_25899.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___3151_25899.FStar_Syntax_Syntax.vars)
          }
      | FStar_Syntax_Syntax.Comp ct ->
          let l =
            FStar_TypeChecker_Env.norm_eff_name
              cfg.FStar_TypeChecker_Cfg.tcenv
              ct.FStar_Syntax_Syntax.effect_name
             in
          let uu____25906 =
            (FStar_Syntax_Util.is_ghost_effect l) &&
              (non_info ct.FStar_Syntax_Syntax.result_typ)
             in
          if uu____25906
          then
            let ct1 =
              let uu____25910 =
                downgrade_ghost_effect_name
                  ct.FStar_Syntax_Syntax.effect_name
                 in
              match uu____25910 with
              | FStar_Pervasives_Native.Some pure_eff ->
                  let flags =
                    let uu____25917 =
                      FStar_Ident.lid_equals pure_eff
                        FStar_Parser_Const.effect_Tot_lid
                       in
                    if uu____25917
                    then FStar_Syntax_Syntax.TOTAL ::
                      (ct.FStar_Syntax_Syntax.flags)
                    else ct.FStar_Syntax_Syntax.flags  in
                  let uu___3161_25924 = ct  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3161_25924.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name = pure_eff;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3161_25924.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3161_25924.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags = flags
                  }
              | FStar_Pervasives_Native.None  ->
                  let ct1 =
                    FStar_TypeChecker_Env.unfold_effect_abbrev
                      cfg.FStar_TypeChecker_Cfg.tcenv c
                     in
                  let uu___3165_25926 = ct1  in
                  {
                    FStar_Syntax_Syntax.comp_univs =
                      (uu___3165_25926.FStar_Syntax_Syntax.comp_univs);
                    FStar_Syntax_Syntax.effect_name =
                      FStar_Parser_Const.effect_PURE_lid;
                    FStar_Syntax_Syntax.result_typ =
                      (uu___3165_25926.FStar_Syntax_Syntax.result_typ);
                    FStar_Syntax_Syntax.effect_args =
                      (uu___3165_25926.FStar_Syntax_Syntax.effect_args);
                    FStar_Syntax_Syntax.flags =
                      (uu___3165_25926.FStar_Syntax_Syntax.flags)
                  }
               in
            let uu___3168_25927 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___3168_25927.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___3168_25927.FStar_Syntax_Syntax.vars)
            }
          else c
      | uu____25930 -> c
  
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
        let uu____25950 = norm cfg [] [] t  in
        FStar_Syntax_Util.non_informative uu____25950  in
      let uu____25957 =
        (FStar_Syntax_Util.is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
          && (non_info lc.FStar_Syntax_Syntax.res_typ)
         in
      if uu____25957
      then
        let uu____25960 =
          downgrade_ghost_effect_name lc.FStar_Syntax_Syntax.eff_name  in
        match uu____25960 with
        | FStar_Pervasives_Native.Some pure_eff ->
            FStar_Syntax_Syntax.mk_lcomp pure_eff
              lc.FStar_Syntax_Syntax.res_typ lc.FStar_Syntax_Syntax.cflags
              (fun uu____25966  ->
                 let uu____25967 = FStar_Syntax_Syntax.lcomp_comp lc  in
                 ghost_to_pure env uu____25967)
        | FStar_Pervasives_Native.None  -> lc
      else lc
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun env  ->
    fun t  ->
      let t1 =
        try
          (fun uu___3184_25984  ->
             match () with
             | () ->
                 normalize [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                   t) ()
        with
        | uu___3183_25987 ->
            ((let uu____25989 =
                let uu____25995 =
                  let uu____25997 = FStar_Util.message_of_exn uu___3183_25987
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____25997
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____25995)  in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____25989);
             t)
         in
      FStar_Syntax_Print.term_to_string' env.FStar_TypeChecker_Env.dsenv t1
  
let (comp_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.comp -> Prims.string) =
  fun env  ->
    fun c  ->
      let c1 =
        try
          (fun uu___3194_26016  ->
             match () with
             | () ->
                 let uu____26017 =
                   FStar_TypeChecker_Cfg.config
                     [FStar_TypeChecker_Env.AllowUnboundUniverses] env
                    in
                 norm_comp uu____26017 [] c) ()
        with
        | uu___3193_26026 ->
            ((let uu____26028 =
                let uu____26034 =
                  let uu____26036 = FStar_Util.message_of_exn uu___3193_26026
                     in
                  FStar_Util.format1 "Normalization failed with error %s\n"
                    uu____26036
                   in
                (FStar_Errors.Warning_NormalizationFailure, uu____26034)  in
              FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu____26028);
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
                   let uu____26085 =
                     let uu____26086 =
                       let uu____26093 =
                         FStar_Syntax_Util.mk_conj_simp phi1 phi  in
                       (y, uu____26093)  in
                     FStar_Syntax_Syntax.Tm_refine uu____26086  in
                   mk uu____26085 t01.FStar_Syntax_Syntax.pos
               | uu____26098 -> t2)
          | uu____26099 -> t2  in
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
        let uu____26193 = FStar_Syntax_Util.arrow_formals_comp t_e  in
        match uu____26193 with
        | (formals,c) ->
            (match formals with
             | [] -> e
             | uu____26230 ->
                 let uu____26239 = FStar_Syntax_Util.abs_formals e  in
                 (match uu____26239 with
                  | (actuals,uu____26249,uu____26250) ->
                      if
                        (FStar_List.length actuals) =
                          (FStar_List.length formals)
                      then e
                      else
                        (let uu____26270 =
                           FStar_All.pipe_right formals
                             FStar_Syntax_Util.args_of_binders
                            in
                         match uu____26270 with
                         | (binders,args) ->
                             let uu____26281 =
                               FStar_Syntax_Syntax.mk_Tm_app e args
                                 FStar_Pervasives_Native.None
                                 e.FStar_Syntax_Syntax.pos
                                in
                             FStar_Syntax_Util.abs binders uu____26281
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
      | uu____26296 ->
          let uu____26297 = FStar_Syntax_Util.head_and_args t  in
          (match uu____26297 with
           | (head1,args) ->
               let uu____26340 =
                 let uu____26341 = FStar_Syntax_Subst.compress head1  in
                 uu____26341.FStar_Syntax_Syntax.n  in
               (match uu____26340 with
                | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
                    let uu____26362 =
                      let uu____26377 =
                        FStar_Syntax_Subst.subst' s
                          u.FStar_Syntax_Syntax.ctx_uvar_typ
                         in
                      FStar_Syntax_Util.arrow_formals uu____26377  in
                    (match uu____26362 with
                     | (formals,_tres) ->
                         if
                           (FStar_List.length formals) =
                             (FStar_List.length args)
                         then t
                         else
                           (let uu____26417 =
                              env.FStar_TypeChecker_Env.type_of
                                (let uu___3264_26425 = env  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___3264_26425.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___3264_26425.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___3264_26425.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___3264_26425.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___3264_26425.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___3264_26425.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___3264_26425.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     FStar_Pervasives_Native.None;
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___3264_26425.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___3264_26425.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___3264_26425.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___3264_26425.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___3264_26425.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___3264_26425.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___3264_26425.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___3264_26425.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___3264_26425.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___3264_26425.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___3264_26425.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___3264_26425.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___3264_26425.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___3264_26425.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___3264_26425.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___3264_26425.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___3264_26425.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___3264_26425.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___3264_26425.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___3264_26425.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___3264_26425.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts = true;
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___3264_26425.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___3264_26425.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___3264_26425.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___3264_26425.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___3264_26425.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___3264_26425.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___3264_26425.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___3264_26425.FStar_TypeChecker_Env.is_native_tactic);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___3264_26425.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___3264_26425.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___3264_26425.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___3264_26425.FStar_TypeChecker_Env.nbe)
                                 }) t
                               in
                            match uu____26417 with
                            | (uu____26428,ty,uu____26430) ->
                                eta_expand_with_type env t ty))
                | uu____26431 ->
                    let uu____26432 =
                      env.FStar_TypeChecker_Env.type_of
                        (let uu___3271_26440 = env  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___3271_26440.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___3271_26440.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___3271_26440.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___3271_26440.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_sig =
                             (uu___3271_26440.FStar_TypeChecker_Env.gamma_sig);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___3271_26440.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___3271_26440.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             FStar_Pervasives_Native.None;
                           FStar_TypeChecker_Env.sigtab =
                             (uu___3271_26440.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.attrtab =
                             (uu___3271_26440.FStar_TypeChecker_Env.attrtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___3271_26440.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___3271_26440.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___3271_26440.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___3271_26440.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___3271_26440.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___3271_26440.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___3271_26440.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___3271_26440.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___3271_26440.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___3271_26440.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___3271_26440.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.phase1 =
                             (uu___3271_26440.FStar_TypeChecker_Env.phase1);
                           FStar_TypeChecker_Env.failhard =
                             (uu___3271_26440.FStar_TypeChecker_Env.failhard);
                           FStar_TypeChecker_Env.nosynth =
                             (uu___3271_26440.FStar_TypeChecker_Env.nosynth);
                           FStar_TypeChecker_Env.uvar_subtyping =
                             (uu___3271_26440.FStar_TypeChecker_Env.uvar_subtyping);
                           FStar_TypeChecker_Env.tc_term =
                             (uu___3271_26440.FStar_TypeChecker_Env.tc_term);
                           FStar_TypeChecker_Env.type_of =
                             (uu___3271_26440.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___3271_26440.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.check_type_of =
                             (uu___3271_26440.FStar_TypeChecker_Env.check_type_of);
                           FStar_TypeChecker_Env.use_bv_sorts = true;
                           FStar_TypeChecker_Env.qtbl_name_and_index =
                             (uu___3271_26440.FStar_TypeChecker_Env.qtbl_name_and_index);
                           FStar_TypeChecker_Env.normalized_eff_names =
                             (uu___3271_26440.FStar_TypeChecker_Env.normalized_eff_names);
                           FStar_TypeChecker_Env.fv_delta_depths =
                             (uu___3271_26440.FStar_TypeChecker_Env.fv_delta_depths);
                           FStar_TypeChecker_Env.proof_ns =
                             (uu___3271_26440.FStar_TypeChecker_Env.proof_ns);
                           FStar_TypeChecker_Env.synth_hook =
                             (uu___3271_26440.FStar_TypeChecker_Env.synth_hook);
                           FStar_TypeChecker_Env.splice =
                             (uu___3271_26440.FStar_TypeChecker_Env.splice);
                           FStar_TypeChecker_Env.postprocess =
                             (uu___3271_26440.FStar_TypeChecker_Env.postprocess);
                           FStar_TypeChecker_Env.is_native_tactic =
                             (uu___3271_26440.FStar_TypeChecker_Env.is_native_tactic);
                           FStar_TypeChecker_Env.identifier_info =
                             (uu___3271_26440.FStar_TypeChecker_Env.identifier_info);
                           FStar_TypeChecker_Env.tc_hooks =
                             (uu___3271_26440.FStar_TypeChecker_Env.tc_hooks);
                           FStar_TypeChecker_Env.dsenv =
                             (uu___3271_26440.FStar_TypeChecker_Env.dsenv);
                           FStar_TypeChecker_Env.nbe =
                             (uu___3271_26440.FStar_TypeChecker_Env.nbe)
                         }) t
                       in
                    (match uu____26432 with
                     | (uu____26443,ty,uu____26445) ->
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
      let uu___3283_26527 = x  in
      let uu____26528 = elim_delayed_subst_term x.FStar_Syntax_Syntax.sort
         in
      {
        FStar_Syntax_Syntax.ppname =
          (uu___3283_26527.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index =
          (uu___3283_26527.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu____26528
      }  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____26531 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_bvar uu____26555 -> t1
    | FStar_Syntax_Syntax.Tm_name uu____26556 -> t1
    | FStar_Syntax_Syntax.Tm_fvar uu____26557 -> t1
    | FStar_Syntax_Syntax.Tm_uinst uu____26558 -> t1
    | FStar_Syntax_Syntax.Tm_constant uu____26565 -> t1
    | FStar_Syntax_Syntax.Tm_type uu____26566 -> t1
    | FStar_Syntax_Syntax.Tm_lazy uu____26567 -> t1
    | FStar_Syntax_Syntax.Tm_unknown  -> t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t2,rc_opt) ->
        let elim_rc rc =
          let uu___3309_26601 = rc  in
          let uu____26602 =
            FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
              elim_delayed_subst_term
             in
          let uu____26611 =
            elim_delayed_subst_cflags rc.FStar_Syntax_Syntax.residual_flags
             in
          {
            FStar_Syntax_Syntax.residual_effect =
              (uu___3309_26601.FStar_Syntax_Syntax.residual_effect);
            FStar_Syntax_Syntax.residual_typ = uu____26602;
            FStar_Syntax_Syntax.residual_flags = uu____26611
          }  in
        let uu____26614 =
          let uu____26615 =
            let uu____26634 = elim_delayed_subst_binders bs  in
            let uu____26643 = elim_delayed_subst_term t2  in
            let uu____26646 = FStar_Util.map_opt rc_opt elim_rc  in
            (uu____26634, uu____26643, uu____26646)  in
          FStar_Syntax_Syntax.Tm_abs uu____26615  in
        mk1 uu____26614
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____26683 =
          let uu____26684 =
            let uu____26699 = elim_delayed_subst_binders bs  in
            let uu____26708 = elim_delayed_subst_comp c  in
            (uu____26699, uu____26708)  in
          FStar_Syntax_Syntax.Tm_arrow uu____26684  in
        mk1 uu____26683
    | FStar_Syntax_Syntax.Tm_refine (bv,phi) ->
        let uu____26727 =
          let uu____26728 =
            let uu____26735 = elim_bv bv  in
            let uu____26736 = elim_delayed_subst_term phi  in
            (uu____26735, uu____26736)  in
          FStar_Syntax_Syntax.Tm_refine uu____26728  in
        mk1 uu____26727
    | FStar_Syntax_Syntax.Tm_app (t2,args) ->
        let uu____26767 =
          let uu____26768 =
            let uu____26785 = elim_delayed_subst_term t2  in
            let uu____26788 = elim_delayed_subst_args args  in
            (uu____26785, uu____26788)  in
          FStar_Syntax_Syntax.Tm_app uu____26768  in
        mk1 uu____26767
    | FStar_Syntax_Syntax.Tm_match (t2,branches) ->
        let rec elim_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_var x ->
              let uu___3331_26860 = p  in
              let uu____26861 =
                let uu____26862 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_var uu____26862  in
              {
                FStar_Syntax_Syntax.v = uu____26861;
                FStar_Syntax_Syntax.p =
                  (uu___3331_26860.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_wild x ->
              let uu___3335_26864 = p  in
              let uu____26865 =
                let uu____26866 = elim_bv x  in
                FStar_Syntax_Syntax.Pat_wild uu____26866  in
              {
                FStar_Syntax_Syntax.v = uu____26865;
                FStar_Syntax_Syntax.p =
                  (uu___3335_26864.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_dot_term (x,t0) ->
              let uu___3341_26873 = p  in
              let uu____26874 =
                let uu____26875 =
                  let uu____26882 = elim_bv x  in
                  let uu____26883 = elim_delayed_subst_term t0  in
                  (uu____26882, uu____26883)  in
                FStar_Syntax_Syntax.Pat_dot_term uu____26875  in
              {
                FStar_Syntax_Syntax.v = uu____26874;
                FStar_Syntax_Syntax.p =
                  (uu___3341_26873.FStar_Syntax_Syntax.p)
              }
          | FStar_Syntax_Syntax.Pat_cons (fv,pats) ->
              let uu___3347_26908 = p  in
              let uu____26909 =
                let uu____26910 =
                  let uu____26924 =
                    FStar_List.map
                      (fun uu____26950  ->
                         match uu____26950 with
                         | (x,b) ->
                             let uu____26967 = elim_pat x  in
                             (uu____26967, b)) pats
                     in
                  (fv, uu____26924)  in
                FStar_Syntax_Syntax.Pat_cons uu____26910  in
              {
                FStar_Syntax_Syntax.v = uu____26909;
                FStar_Syntax_Syntax.p =
                  (uu___3347_26908.FStar_Syntax_Syntax.p)
              }
          | uu____26982 -> p  in
        let elim_branch uu____27006 =
          match uu____27006 with
          | (pat,wopt,t3) ->
              let uu____27032 = elim_pat pat  in
              let uu____27035 =
                FStar_Util.map_opt wopt elim_delayed_subst_term  in
              let uu____27038 = elim_delayed_subst_term t3  in
              (uu____27032, uu____27035, uu____27038)
           in
        let uu____27043 =
          let uu____27044 =
            let uu____27067 = elim_delayed_subst_term t2  in
            let uu____27070 = FStar_List.map elim_branch branches  in
            (uu____27067, uu____27070)  in
          FStar_Syntax_Syntax.Tm_match uu____27044  in
        mk1 uu____27043
    | FStar_Syntax_Syntax.Tm_ascribed (t2,a,lopt) ->
        let elim_ascription uu____27201 =
          match uu____27201 with
          | (tc,topt) ->
              let uu____27236 =
                match tc with
                | FStar_Util.Inl t3 ->
                    let uu____27246 = elim_delayed_subst_term t3  in
                    FStar_Util.Inl uu____27246
                | FStar_Util.Inr c ->
                    let uu____27248 = elim_delayed_subst_comp c  in
                    FStar_Util.Inr uu____27248
                 in
              let uu____27249 =
                FStar_Util.map_opt topt elim_delayed_subst_term  in
              (uu____27236, uu____27249)
           in
        let uu____27258 =
          let uu____27259 =
            let uu____27286 = elim_delayed_subst_term t2  in
            let uu____27289 = elim_ascription a  in
            (uu____27286, uu____27289, lopt)  in
          FStar_Syntax_Syntax.Tm_ascribed uu____27259  in
        mk1 uu____27258
    | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
        let elim_lb lb =
          let uu___3377_27352 = lb  in
          let uu____27353 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____27356 =
            elim_delayed_subst_term lb.FStar_Syntax_Syntax.lbdef  in
          {
            FStar_Syntax_Syntax.lbname =
              (uu___3377_27352.FStar_Syntax_Syntax.lbname);
            FStar_Syntax_Syntax.lbunivs =
              (uu___3377_27352.FStar_Syntax_Syntax.lbunivs);
            FStar_Syntax_Syntax.lbtyp = uu____27353;
            FStar_Syntax_Syntax.lbeff =
              (uu___3377_27352.FStar_Syntax_Syntax.lbeff);
            FStar_Syntax_Syntax.lbdef = uu____27356;
            FStar_Syntax_Syntax.lbattrs =
              (uu___3377_27352.FStar_Syntax_Syntax.lbattrs);
            FStar_Syntax_Syntax.lbpos =
              (uu___3377_27352.FStar_Syntax_Syntax.lbpos)
          }  in
        let uu____27359 =
          let uu____27360 =
            let uu____27374 =
              let uu____27382 =
                FStar_List.map elim_lb (FStar_Pervasives_Native.snd lbs)  in
              ((FStar_Pervasives_Native.fst lbs), uu____27382)  in
            let uu____27394 = elim_delayed_subst_term t2  in
            (uu____27374, uu____27394)  in
          FStar_Syntax_Syntax.Tm_let uu____27360  in
        mk1 uu____27359
    | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
        mk1 (FStar_Syntax_Syntax.Tm_uvar (u, s))
    | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
        let qi1 =
          FStar_Syntax_Syntax.on_antiquoted elim_delayed_subst_term qi  in
        let uu____27439 =
          let uu____27440 =
            let uu____27447 = elim_delayed_subst_term tm  in
            (uu____27447, qi1)  in
          FStar_Syntax_Syntax.Tm_quoted uu____27440  in
        mk1 uu____27439
    | FStar_Syntax_Syntax.Tm_meta (t2,md) ->
        let uu____27458 =
          let uu____27459 =
            let uu____27466 = elim_delayed_subst_term t2  in
            let uu____27469 = elim_delayed_subst_meta md  in
            (uu____27466, uu____27469)  in
          FStar_Syntax_Syntax.Tm_meta uu____27459  in
        mk1 uu____27458

and (elim_delayed_subst_cflags :
  FStar_Syntax_Syntax.cflag Prims.list ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun flags  ->
    FStar_List.map
      (fun uu___18_27478  ->
         match uu___18_27478 with
         | FStar_Syntax_Syntax.DECREASES t ->
             let uu____27482 = elim_delayed_subst_term t  in
             FStar_Syntax_Syntax.DECREASES uu____27482
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
        let uu____27505 =
          let uu____27506 =
            let uu____27515 = elim_delayed_subst_term t  in
            (uu____27515, uopt)  in
          FStar_Syntax_Syntax.Total uu____27506  in
        mk1 uu____27505
    | FStar_Syntax_Syntax.GTotal (t,uopt) ->
        let uu____27532 =
          let uu____27533 =
            let uu____27542 = elim_delayed_subst_term t  in
            (uu____27542, uopt)  in
          FStar_Syntax_Syntax.GTotal uu____27533  in
        mk1 uu____27532
    | FStar_Syntax_Syntax.Comp ct ->
        let ct1 =
          let uu___3410_27551 = ct  in
          let uu____27552 =
            elim_delayed_subst_term ct.FStar_Syntax_Syntax.result_typ  in
          let uu____27555 =
            elim_delayed_subst_args ct.FStar_Syntax_Syntax.effect_args  in
          let uu____27566 =
            elim_delayed_subst_cflags ct.FStar_Syntax_Syntax.flags  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___3410_27551.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___3410_27551.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ = uu____27552;
            FStar_Syntax_Syntax.effect_args = uu____27555;
            FStar_Syntax_Syntax.flags = uu____27566
          }  in
        mk1 (FStar_Syntax_Syntax.Comp ct1)

and (elim_delayed_subst_meta :
  FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun uu___19_27569  ->
    match uu___19_27569 with
    | FStar_Syntax_Syntax.Meta_pattern (names1,args,np) ->
        let uu____27607 =
          let uu____27631 = FStar_List.map elim_delayed_subst_term names1  in
          let uu____27640 = FStar_List.map elim_delayed_subst_args args  in
          (uu____27631, uu____27640, np)  in
        FStar_Syntax_Syntax.Meta_pattern uu____27607
    | FStar_Syntax_Syntax.Meta_monadic (m,t) ->
        let uu____27696 =
          let uu____27703 = elim_delayed_subst_term t  in (m, uu____27703)
           in
        FStar_Syntax_Syntax.Meta_monadic uu____27696
    | FStar_Syntax_Syntax.Meta_monadic_lift (m1,m2,t) ->
        let uu____27715 =
          let uu____27724 = elim_delayed_subst_term t  in
          (m1, m2, uu____27724)  in
        FStar_Syntax_Syntax.Meta_monadic_lift uu____27715
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
      (fun uu____27757  ->
         match uu____27757 with
         | (t,q) ->
             let uu____27776 = elim_delayed_subst_term t  in (uu____27776, q))
      args

and (elim_delayed_subst_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun bs  ->
    FStar_List.map
      (fun uu____27804  ->
         match uu____27804 with
         | (x,q) ->
             let uu____27823 =
               let uu___3437_27824 = x  in
               let uu____27825 =
                 elim_delayed_subst_term x.FStar_Syntax_Syntax.sort  in
               {
                 FStar_Syntax_Syntax.ppname =
                   (uu___3437_27824.FStar_Syntax_Syntax.ppname);
                 FStar_Syntax_Syntax.index =
                   (uu___3437_27824.FStar_Syntax_Syntax.index);
                 FStar_Syntax_Syntax.sort = uu____27825
               }  in
             (uu____27823, q)) bs

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
            | (uu____27933,FStar_Util.Inr c) ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_arrow (binders, c))
                  FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
            | (uu____27965,FStar_Util.Inl t) ->
                let uu____27987 =
                  let uu____27994 =
                    let uu____27995 =
                      let uu____28010 = FStar_Syntax_Syntax.mk_Total t  in
                      (binders, uu____28010)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____27995  in
                  FStar_Syntax_Syntax.mk uu____27994  in
                uu____27987 FStar_Pervasives_Native.None
                  t.FStar_Syntax_Syntax.pos
             in
          let uu____28023 = FStar_Syntax_Subst.open_univ_vars univ_names t
             in
          match uu____28023 with
          | (univ_names1,t1) ->
              let t2 = remove_uvar_solutions env t1  in
              let t3 = FStar_Syntax_Subst.close_univ_vars univ_names1 t2  in
              let t4 = elim_delayed_subst_term t3  in
              let uu____28055 =
                match binders with
                | [] -> ([], (FStar_Util.Inl t4))
                | uu____28128 ->
                    let uu____28129 =
                      let uu____28138 =
                        let uu____28139 = FStar_Syntax_Subst.compress t4  in
                        uu____28139.FStar_Syntax_Syntax.n  in
                      (uu____28138, tc)  in
                    (match uu____28129 with
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inr uu____28168) ->
                         (binders1, (FStar_Util.Inr c))
                     | (FStar_Syntax_Syntax.Tm_arrow
                        (binders1,c),FStar_Util.Inl uu____28215) ->
                         (binders1,
                           (FStar_Util.Inl (FStar_Syntax_Util.comp_result c)))
                     | (uu____28260,FStar_Util.Inl uu____28261) ->
                         ([], (FStar_Util.Inl t4))
                     | uu____28292 -> failwith "Impossible")
                 in
              (match uu____28055 with
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
          let uu____28431 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inl t)  in
          match uu____28431 with
          | (univ_names1,binders1,tc) ->
              let uu____28505 = FStar_Util.left tc  in
              (univ_names1, binders1, uu____28505)
  
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
          let uu____28559 =
            elim_uvars_aux_tc env univ_names binders (FStar_Util.Inr c)  in
          match uu____28559 with
          | (univ_names1,binders1,tc) ->
              let uu____28633 = FStar_Util.right tc  in
              (univ_names1, binders1, uu____28633)
  
let rec (elim_uvars :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun s  ->
      match s.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (lid,univ_names,binders,typ,lids,lids') ->
          let uu____28675 = elim_uvars_aux_t env univ_names binders typ  in
          (match uu____28675 with
           | (univ_names1,binders1,typ1) ->
               let uu___3520_28715 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_inductive_typ
                      (lid, univ_names1, binders1, typ1, lids, lids'));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3520_28715.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3520_28715.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3520_28715.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3520_28715.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
          let uu___3526_28730 = s  in
          let uu____28731 =
            let uu____28732 =
              let uu____28741 = FStar_List.map (elim_uvars env) sigs  in
              (uu____28741, lids)  in
            FStar_Syntax_Syntax.Sig_bundle uu____28732  in
          {
            FStar_Syntax_Syntax.sigel = uu____28731;
            FStar_Syntax_Syntax.sigrng =
              (uu___3526_28730.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3526_28730.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3526_28730.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3526_28730.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_datacon (lid,univ_names,typ,lident,i,lids) ->
          let uu____28760 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28760 with
           | (univ_names1,uu____28784,typ1) ->
               let uu___3540_28806 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_datacon
                      (lid, univ_names1, typ1, lident, i, lids));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3540_28806.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3540_28806.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3540_28806.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3540_28806.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univ_names,typ) ->
          let uu____28813 = elim_uvars_aux_t env univ_names [] typ  in
          (match uu____28813 with
           | (univ_names1,uu____28837,typ1) ->
               let uu___3551_28859 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_declare_typ
                      (lid, univ_names1, typ1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3551_28859.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3551_28859.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3551_28859.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3551_28859.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
          let lbs1 =
            FStar_All.pipe_right lbs
              (FStar_List.map
                 (fun lb  ->
                    let uu____28889 =
                      FStar_Syntax_Subst.univ_var_opening
                        lb.FStar_Syntax_Syntax.lbunivs
                       in
                    match uu____28889 with
                    | (opening,lbunivs) ->
                        let elim t =
                          let uu____28914 =
                            let uu____28915 =
                              let uu____28916 =
                                FStar_Syntax_Subst.subst opening t  in
                              remove_uvar_solutions env uu____28916  in
                            FStar_Syntax_Subst.close_univ_vars lbunivs
                              uu____28915
                             in
                          elim_delayed_subst_term uu____28914  in
                        let lbtyp = elim lb.FStar_Syntax_Syntax.lbtyp  in
                        let lbdef = elim lb.FStar_Syntax_Syntax.lbdef  in
                        let uu___3567_28919 = lb  in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___3567_28919.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = lbunivs;
                          FStar_Syntax_Syntax.lbtyp = lbtyp;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___3567_28919.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = lbdef;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___3567_28919.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___3567_28919.FStar_Syntax_Syntax.lbpos)
                        }))
             in
          let uu___3570_28920 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_let ((b, lbs1), lids));
            FStar_Syntax_Syntax.sigrng =
              (uu___3570_28920.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3570_28920.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3570_28920.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3570_28920.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_main t ->
          let uu___3574_28927 = s  in
          let uu____28928 =
            let uu____28929 = remove_uvar_solutions env t  in
            FStar_Syntax_Syntax.Sig_main uu____28929  in
          {
            FStar_Syntax_Syntax.sigel = uu____28928;
            FStar_Syntax_Syntax.sigrng =
              (uu___3574_28927.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3574_28927.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3574_28927.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3574_28927.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_assume (l,us,t) ->
          let uu____28933 = elim_uvars_aux_t env us [] t  in
          (match uu____28933 with
           | (us1,uu____28957,t1) ->
               let uu___3585_28979 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_assume (l, us1, t1));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3585_28979.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3585_28979.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3585_28979.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3585_28979.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28980 ->
          failwith "Impossible: should have been desugared already"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____28983 =
            elim_uvars_aux_t env ed.FStar_Syntax_Syntax.univs
              ed.FStar_Syntax_Syntax.binders ed.FStar_Syntax_Syntax.signature
             in
          (match uu____28983 with
           | (univs1,binders,signature) ->
               let uu____29023 =
                 let uu____29028 = FStar_Syntax_Subst.univ_var_opening univs1
                    in
                 match uu____29028 with
                 | (univs_opening,univs2) ->
                     let uu____29051 =
                       FStar_Syntax_Subst.univ_var_closing univs2  in
                     (univs_opening, uu____29051)
                  in
               (match uu____29023 with
                | (univs_opening,univs_closing) ->
                    let uu____29054 =
                      let binders1 = FStar_Syntax_Subst.open_binders binders
                         in
                      let uu____29060 =
                        FStar_Syntax_Subst.opening_of_binders binders1  in
                      let uu____29061 =
                        FStar_Syntax_Subst.closing_of_binders binders1  in
                      (uu____29060, uu____29061)  in
                    (match uu____29054 with
                     | (b_opening,b_closing) ->
                         let n1 = FStar_List.length univs1  in
                         let n_binders = FStar_List.length binders  in
                         let elim_tscheme uu____29087 =
                           match uu____29087 with
                           | (us,t) ->
                               let n_us = FStar_List.length us  in
                               let uu____29105 =
                                 FStar_Syntax_Subst.open_univ_vars us t  in
                               (match uu____29105 with
                                | (us1,t1) ->
                                    let uu____29116 =
                                      let uu____29125 =
                                        FStar_All.pipe_right b_opening
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      let uu____29130 =
                                        FStar_All.pipe_right b_closing
                                          (FStar_Syntax_Subst.shift_subst
                                             n_us)
                                         in
                                      (uu____29125, uu____29130)  in
                                    (match uu____29116 with
                                     | (b_opening1,b_closing1) ->
                                         let uu____29153 =
                                           let uu____29162 =
                                             FStar_All.pipe_right
                                               univs_opening
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           let uu____29167 =
                                             FStar_All.pipe_right
                                               univs_closing
                                               (FStar_Syntax_Subst.shift_subst
                                                  n_us)
                                              in
                                           (uu____29162, uu____29167)  in
                                         (match uu____29153 with
                                          | (univs_opening1,univs_closing1)
                                              ->
                                              let t2 =
                                                let uu____29191 =
                                                  FStar_Syntax_Subst.subst
                                                    b_opening1 t1
                                                   in
                                                FStar_Syntax_Subst.subst
                                                  univs_opening1 uu____29191
                                                 in
                                              let uu____29192 =
                                                elim_uvars_aux_t env [] [] t2
                                                 in
                                              (match uu____29192 with
                                               | (uu____29219,uu____29220,t3)
                                                   ->
                                                   let t4 =
                                                     let uu____29243 =
                                                       let uu____29244 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us1 t3
                                                          in
                                                       FStar_Syntax_Subst.subst
                                                         b_closing1
                                                         uu____29244
                                                        in
                                                     FStar_Syntax_Subst.subst
                                                       univs_closing1
                                                       uu____29243
                                                      in
                                                   (us1, t4)))))
                            in
                         let elim_term t =
                           let uu____29253 =
                             elim_uvars_aux_t env univs1 binders t  in
                           match uu____29253 with
                           | (uu____29272,uu____29273,t1) -> t1  in
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
                             | uu____29349 ->
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_abs
                                      ((a.FStar_Syntax_Syntax.action_params),
                                        body, FStar_Pervasives_Native.None))
                                   FStar_Pervasives_Native.None
                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                              in
                           let destruct_action_body body =
                             let uu____29376 =
                               let uu____29377 =
                                 FStar_Syntax_Subst.compress body  in
                               uu____29377.FStar_Syntax_Syntax.n  in
                             match uu____29376 with
                             | FStar_Syntax_Syntax.Tm_ascribed
                                 (defn,(FStar_Util.Inl
                                        typ,FStar_Pervasives_Native.None ),FStar_Pervasives_Native.None
                                  )
                                 -> (defn, typ)
                             | uu____29436 -> failwith "Impossible"  in
                           let destruct_action_typ_templ t =
                             let uu____29470 =
                               let uu____29471 =
                                 FStar_Syntax_Subst.compress t  in
                               uu____29471.FStar_Syntax_Syntax.n  in
                             match uu____29470 with
                             | FStar_Syntax_Syntax.Tm_abs
                                 (pars,body,uu____29494) ->
                                 let uu____29519 = destruct_action_body body
                                    in
                                 (match uu____29519 with
                                  | (defn,typ) -> (pars, defn, typ))
                             | uu____29568 ->
                                 let uu____29569 = destruct_action_body t  in
                                 (match uu____29569 with
                                  | (defn,typ) -> ([], defn, typ))
                              in
                           let uu____29624 =
                             elim_tscheme
                               ((a.FStar_Syntax_Syntax.action_univs),
                                 action_typ_templ)
                              in
                           match uu____29624 with
                           | (action_univs,t) ->
                               let uu____29633 = destruct_action_typ_templ t
                                  in
                               (match uu____29633 with
                                | (action_params,action_defn,action_typ) ->
                                    let a' =
                                      let uu___3671_29680 = a  in
                                      {
                                        FStar_Syntax_Syntax.action_name =
                                          (uu___3671_29680.FStar_Syntax_Syntax.action_name);
                                        FStar_Syntax_Syntax.action_unqualified_name
                                          =
                                          (uu___3671_29680.FStar_Syntax_Syntax.action_unqualified_name);
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
                           let uu___3674_29682 = ed  in
                           let uu____29683 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ret_wp  in
                           let uu____29684 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                           let uu____29685 =
                             elim_tscheme ed.FStar_Syntax_Syntax.if_then_else
                              in
                           let uu____29686 =
                             elim_tscheme ed.FStar_Syntax_Syntax.ite_wp  in
                           let uu____29687 =
                             elim_tscheme ed.FStar_Syntax_Syntax.stronger  in
                           let uu____29688 =
                             elim_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                           let uu____29689 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assert_p  in
                           let uu____29690 =
                             elim_tscheme ed.FStar_Syntax_Syntax.assume_p  in
                           let uu____29691 =
                             elim_tscheme ed.FStar_Syntax_Syntax.null_wp  in
                           let uu____29692 =
                             elim_tscheme ed.FStar_Syntax_Syntax.trivial  in
                           let uu____29693 =
                             elim_term ed.FStar_Syntax_Syntax.repr  in
                           let uu____29694 =
                             elim_tscheme ed.FStar_Syntax_Syntax.return_repr
                              in
                           let uu____29695 =
                             elim_tscheme ed.FStar_Syntax_Syntax.bind_repr
                              in
                           let uu____29696 =
                             FStar_List.map elim_action
                               ed.FStar_Syntax_Syntax.actions
                              in
                           {
                             FStar_Syntax_Syntax.cattributes =
                               (uu___3674_29682.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.mname =
                               (uu___3674_29682.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.univs = univs1;
                             FStar_Syntax_Syntax.binders = binders;
                             FStar_Syntax_Syntax.signature = signature;
                             FStar_Syntax_Syntax.ret_wp = uu____29683;
                             FStar_Syntax_Syntax.bind_wp = uu____29684;
                             FStar_Syntax_Syntax.if_then_else = uu____29685;
                             FStar_Syntax_Syntax.ite_wp = uu____29686;
                             FStar_Syntax_Syntax.stronger = uu____29687;
                             FStar_Syntax_Syntax.close_wp = uu____29688;
                             FStar_Syntax_Syntax.assert_p = uu____29689;
                             FStar_Syntax_Syntax.assume_p = uu____29690;
                             FStar_Syntax_Syntax.null_wp = uu____29691;
                             FStar_Syntax_Syntax.trivial = uu____29692;
                             FStar_Syntax_Syntax.repr = uu____29693;
                             FStar_Syntax_Syntax.return_repr = uu____29694;
                             FStar_Syntax_Syntax.bind_repr = uu____29695;
                             FStar_Syntax_Syntax.actions = uu____29696;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___3674_29682.FStar_Syntax_Syntax.eff_attrs)
                           }  in
                         let uu___3677_29699 = s  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_new_effect ed1);
                           FStar_Syntax_Syntax.sigrng =
                             (uu___3677_29699.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals =
                             (uu___3677_29699.FStar_Syntax_Syntax.sigquals);
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___3677_29699.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___3677_29699.FStar_Syntax_Syntax.sigattrs)
                         })))
      | FStar_Syntax_Syntax.Sig_sub_effect sub_eff ->
          let elim_tscheme_opt uu___20_29720 =
            match uu___20_29720 with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (us,t) ->
                let uu____29751 = elim_uvars_aux_t env us [] t  in
                (match uu____29751 with
                 | (us1,uu____29783,t1) ->
                     FStar_Pervasives_Native.Some (us1, t1))
             in
          let sub_eff1 =
            let uu___3692_29814 = sub_eff  in
            let uu____29815 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift_wp  in
            let uu____29818 =
              elim_tscheme_opt sub_eff.FStar_Syntax_Syntax.lift  in
            {
              FStar_Syntax_Syntax.source =
                (uu___3692_29814.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target =
                (uu___3692_29814.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu____29815;
              FStar_Syntax_Syntax.lift = uu____29818
            }  in
          let uu___3695_29821 = s  in
          {
            FStar_Syntax_Syntax.sigel =
              (FStar_Syntax_Syntax.Sig_sub_effect sub_eff1);
            FStar_Syntax_Syntax.sigrng =
              (uu___3695_29821.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals =
              (uu___3695_29821.FStar_Syntax_Syntax.sigquals);
            FStar_Syntax_Syntax.sigmeta =
              (uu___3695_29821.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs =
              (uu___3695_29821.FStar_Syntax_Syntax.sigattrs)
          }
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          (lid,univ_names,binders,comp,flags) ->
          let uu____29831 = elim_uvars_aux_c env univ_names binders comp  in
          (match uu____29831 with
           | (univ_names1,binders1,comp1) ->
               let uu___3708_29871 = s  in
               {
                 FStar_Syntax_Syntax.sigel =
                   (FStar_Syntax_Syntax.Sig_effect_abbrev
                      (lid, univ_names1, binders1, comp1, flags));
                 FStar_Syntax_Syntax.sigrng =
                   (uu___3708_29871.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___3708_29871.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___3708_29871.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___3708_29871.FStar_Syntax_Syntax.sigattrs)
               })
      | FStar_Syntax_Syntax.Sig_pragma uu____29874 -> s
      | FStar_Syntax_Syntax.Sig_splice uu____29875 -> s
  
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
        let uu____29924 =
          FStar_TypeChecker_Env.lookup_nonrec_definition
            [FStar_TypeChecker_Env.Unfold FStar_Syntax_Syntax.delta_constant]
            env (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____29924 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some head_def_ts ->
            let uu____29946 =
              FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us  in
            (match uu____29946 with
             | (uu____29953,head_def) ->
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
      let uu____29959 = FStar_Syntax_Util.head_and_args t  in
      match uu____29959 with
      | (head1,args) ->
          let uu____30004 =
            let uu____30005 = FStar_Syntax_Subst.compress head1  in
            uu____30005.FStar_Syntax_Syntax.n  in
          (match uu____30004 with
           | FStar_Syntax_Syntax.Tm_fvar fv -> aux fv [] args
           | FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                  FStar_Syntax_Syntax.pos = uu____30012;
                  FStar_Syntax_Syntax.vars = uu____30013;_},us)
               -> aux fv us args
           | uu____30019 -> FStar_Pervasives_Native.None)
  